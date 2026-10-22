/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusCutoff
public import LeanFun.Mathlib.MeasureTheory.Function.L2Space.MeasureCongr

/-! # Annular energy vectors belong to the zero-boundary Sobolev graph

Smooth cutoff approximation puts polynomial trials in the standard Dirichlet
graph. Radial density and the angular Hilbert sum extend this inclusion to all
completed energy vectors. This is one direction of the Sobolev identification.
Reference: Evans, *Partial Differential Equations*, Chapter 5.
-/

@[expose] public noncomputable section
open MeasureTheory
open Set Filter
open scoped Topology
namespace MvPolynomial.AnnularEnergy

/-- The equality of polar and area measures identifies their function/gradient spaces. -/
def areaGraphEquiv (q : Ioo (0 : ℝ) 1) :
    PhysicalL2 q × GradientL2 q ≃ₗᵢ[ℝ]
      DirichletSpace.FunctionL2 (domain q) × DirichletSpace.GradientL2 (domain q) :=
  L2.graphMeasureCongr 2 (zernikeAnnulusMeasure_zero_zero_eq_volume q.property)

/-- The Cartesian gradient of a smooth test in the physical L² spaces. -/
def physicalTestGradient (q : Ioo (0 : ℝ) 1) :
    TestFunction (domain q) ℝ ⊤ →ₗ[ℝ] GradientL2 q :=
  ∑ i : Fin 2, (lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 ↦ PhysicalL2 q) 2 i).toLinearMap.comp
    ((physicalTestL2 q).comp (DirichletSpace.testDerivative (domain q) i).toLinearMap)

/-- Measure transport preserves the graph of a smooth compactly supported test. -/
theorem areaGraphEquiv_testGraph (q : Ioo (0 : ℝ) 1)
    (φ : TestFunction (domain q) ℝ ⊤) :
    areaGraphEquiv q (physicalTestL2 q φ, physicalTestGradient q φ) =
      DirichletSpace.testGraph (domain q) φ := by
  simp only [physicalTestGradient, DirichletSpace.testGraph, DirichletSpace.testGradient,
    LinearMap.prod_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, lp.singleContinuousLinearMap_apply]
  exact L2.graphMeasureCongr_toLp 2 _ φ
    (fun i ↦ DirichletSpace.testDerivative (domain q) i φ)
    (test_memLp q φ) (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
    (fun i ↦ test_memLp q _)
    (fun i ↦ (DirichletSpace.testDerivative (domain q) i φ).continuous.memLp_of_hasCompactSupport
      (DirichletSpace.testDerivative (domain q) i φ).hasCompactSupport)

/-- The full Cartesian gradient of the smooth cutoffs converges in the Hilbert sum. -/
theorem tendsto_cutoffTest_gradient_L2 (q : Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) :
    Tendsto (fun n ↦ physicalTestGradient q (cutoffTest q p n)) atTop
      (𝓝 (polynomialGradient q (annulusBoundaryWeight q*p))) := by
  have h : Tendsto (fun n ↦ ∑ i : Fin 2, lp.single 2 i
      (physicalTestL2 q (DirichletSpace.testDerivative (domain q) i (cutoffTest q p n)))) atTop
      (𝓝 (∑ i : Fin 2, lp.single 2 i
        (polynomialToL2 (physicalMeasure_moments q) (pderiv i (annulusBoundaryWeight q*p))))) := by
    apply tendsto_finsetSum
    intro i _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 ↦ PhysicalL2 q) 2 i).continuous.tendsto _
      |>.comp (tendsto_cutoffTest_derivative_L2 q p i)
  simpa [physicalTestGradient, polynomialGradient, Fin.sum_univ_two] using h

/-- Every boundary-vanishing Cartesian polynomial belongs to the zero-boundary graph. -/
theorem polynomialGraph_mem_dirichlet (q : Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) :
    areaGraphEquiv q (polynomialToL2 (physicalMeasure_moments q) (annulusBoundaryWeight q*p),
      polynomialGradient q (annulusBoundaryWeight q*p)) ∈ DirichletSpace.graph (domain q) := by
  have ht := (areaGraphEquiv q).continuous.tendsto _ |>.comp
    ((tendsto_cutoffTest_L2 q p).prodMk_nhds (tendsto_cutoffTest_gradient_L2 q p))
  apply (DirichletSpace.graph_isClosed (domain q)).mem_of_tendsto ht
  exact Filter.Eventually.of_forall (fun n ↦ by
    dsimp only [Function.comp_apply]
    rw [areaGraphEquiv_testGraph]
    exact DirichletSpace.testGraph_mem (domain q) _)

/-- Every completed annular energy vector belongs to the zero-boundary Sobolev graph. -/
theorem functionGradient_mem_dirichlet (q : Ioo (0 : ℝ) 1) (x : Space q) :
    areaGraphEquiv q (functionGradient q x) ∈ DirichletSpace.graph (domain q) := by
  let S : Submodule ℝ (Space q) := (DirichletSpace.graph (domain q)).comap
    ((areaGraphEquiv q).toLinearMap.comp (functionGradient q).toLinearMap)
  have hS : IsClosed (S : Set (Space q)) :=
    (DirichletSpace.graph_isClosed (domain q)).preimage
      ((areaGraphEquiv q).continuous.comp (functionGradient q).continuous)
  have hp (s : Sector) (p : Polynomial ℝ) : polynomialEmbed q s p ∈ S := by
    have h := polynomialGraph_mem_dirichlet q (annulusLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p)
    change areaGraphEquiv q (physicalL2 q (polynomialEmbed q s p),
      gradientL2 q (polynomialEmbed q s p)) ∈ DirichletSpace.graph (domain q)
    rw [physicalL2_polynomialEmbed, gradientL2_polynomialEmbed]
    exact h
  have hs (s : Sector) (y : RadialSpace q s) : sectorEmbed q s y ∈ S := by
    refine (Polynomial.SemiclassicalJacobiEnergy.denseRange_polynomialEmbed
      (parameter q) s.val.2).induction ?_ (hS.preimage (sectorEmbed q s).continuous) y
    rintro _ ⟨p, rfl⟩
    have h := hp s p
    simp only [polynomialEmbed, LinearMap.smul_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe] at h
    exact (S.smul_mem_iff
      (Real.sqrt_pos.mpr (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property)).ne').mp h
  apply hS.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x)
  exact Filter.Eventually.of_forall (fun t ↦ S.sum_mem (fun i _ ↦ hs i (x i)))
end MvPolynomial.AnnularEnergy
