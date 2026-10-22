/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusArea
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusGradient
public import LeanFun.Mathlib.Analysis.Calculus.FDeriv.MvPolynomial
/-! # Weak Cartesian derivatives of annular energy vectors

The polar measure is ordinary area measure. Polynomial integration by parts
extends through each radial completion and the angular Hilbert sum. Thus the
completed Cartesian gradient components are weak derivatives against every
smooth compactly supported test in the annulus.
Reference: Evans, *Partial Differential Equations*, Chapter 5; the annular
trial spaces are those of Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open MeasureTheory Set Polynomial
namespace MvPolynomial.AnnularEnergy
/-- The open annulus with squared inner radius q and outer radius one. -/
def domain (q : Ioo (0 : ℝ) 1) : TopologicalSpace.Opens (Fin 2 → ℝ) where
  carrier := {x | (q : ℝ) < x 0^2+x 1^2 ∧ x 0^2+x 1^2 < 1}
  is_open' := by
    have h : Continuous (fun x : Fin 2 → ℝ ↦ x 0^2+x 1^2) := by fun_prop
    exact (isOpen_lt continuous_const h).inter (isOpen_lt h continuous_const)
/-- Smooth compactly supported annular tests are square integrable for the physical measure. -/
theorem test_memLp (q : Ioo (0 : ℝ) 1) (φ : TestFunction (domain q) ℝ ⊤) :
    MemLp φ 2 (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) := by
  rw [zernikeAnnulusMeasure_zero_zero_eq_volume q.property]
  exact φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
/-- A smooth compactly supported annular test as a physical L² class. -/
def physicalTestL2 (q : Ioo (0 : ℝ) 1) :
    TestFunction (domain q) ℝ ⊤ →ₗ[ℝ] PhysicalL2 q where
  toFun φ := (test_memLp q φ).toLp φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- Physical test representatives agree almost everywhere with the smooth test. -/
theorem coe_physicalTestL2 (q : Ioo (0 : ℝ) 1) (φ : TestFunction (domain q) ℝ ⊤) :
    (physicalTestL2 q φ : (Fin 2 → ℝ) → ℝ) =ᵐ[zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0] φ :=
  (test_memLp q φ).coeFn_toLp
/-- Pairing a polynomial with a physical test gives the ordinary Lebesgue integral. -/
theorem inner_polynomial_physicalTestL2 (q : Ioo (0 : ℝ) 1)
    (p : MvPolynomial (Fin 2) ℝ) (φ : TestFunction (domain q) ℝ ⊤) :
    inner ℝ (polynomialToL2 (physicalMeasure_moments q) p) (physicalTestL2 q φ) =
      ∫ x, eval x p * φ x := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, eval x p*φ x ∂zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0 := by
      apply integral_congr_ae
      filter_upwards [coe_polynomialToL2 (physicalMeasure_moments q) p,
        coe_physicalTestL2 q φ] with x hp hφ
      simp [hp, hφ, mul_comm]
    _ = _ := by
      rw [zernikeAnnulusMeasure_zero_zero_eq_volume q.property]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hφ : φ x = 0 := by
        by_contra hn
        exact hx (φ.tsupport_subset (subset_tsupport φ (Function.mem_support.mpr hn)))
      rw [hφ, mul_zero]
/-- Polynomial Cartesian gradients satisfy the weak-derivative identity on the annulus. -/
theorem polynomial_weakDerivative (q : Ioo (0 : ℝ) 1) (p : MvPolynomial (Fin 2) ℝ)
    (φ : TestFunction (domain q) ℝ ⊤) (i : Fin 2) :
    inner ℝ (polynomialToL2 (physicalMeasure_moments q) p)
      (physicalTestL2 q (DirichletSpace.testDerivative (domain q) i φ)) =
      -inner ℝ (polynomialGradient q p i) (physicalTestL2 q φ) := by
  rw [polynomialGradient_apply, inner_polynomial_physicalTestL2,
    inner_polynomial_physicalTestL2]
  exact integral_eval_mul_testDerivative (domain q) p φ i
/-- Every completed annular energy vector has the prescribed Cartesian weak derivatives. -/
theorem gradientL2_weakDerivative (q : Ioo (0 : ℝ) 1) (x : Space q)
    (φ : TestFunction (domain q) ℝ ⊤) (i : Fin 2) :
    inner ℝ (physicalL2 q x)
      (physicalTestL2 q (DirichletSpace.testDerivative (domain q) i φ)) =
      -inner ℝ (gradientL2 q x i) (physicalTestL2 q φ) := by
  let L : Space q →L[ℝ] ℝ :=
    (innerSLFlip ℝ (physicalTestL2 q (DirichletSpace.testDerivative (domain q) i φ))).comp
      (physicalL2 q)
  let R : Space q →L[ℝ] ℝ :=
    -((innerSLFlip ℝ (physicalTestL2 q φ)).comp
      ((lp.evalCLM ℝ (fun _ : Fin 2 ↦ PhysicalL2 q) 2 i).comp
        (gradientL2 q).toContinuousLinearMap))
  have hp (s : Sector) (p : Polynomial ℝ) :
      L (polynomialEmbed q s p) = R (polynomialEmbed q s p) := by
    have h := polynomial_weakDerivative q (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p) φ i
    simpa only [L, R, ContinuousLinearMap.comp_apply, innerSLFlip_apply_apply,
      neg_apply, lp.evalCLM, lp.evalₗ_apply, LinearMap.mkContinuous_apply,
      LinearIsometry.coe_toContinuousLinearMap, physicalL2_polynomialEmbed,
      gradientL2_polynomialEmbed, radialPolynomialL2, LinearMap.comp_apply] using h
  have hLR : L = R := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
    intro s
    apply ContinuousLinearMap.ext
    intro y
    change L (sectorEmbed q s y) = R (sectorEmbed q s y)
    refine (SemiclassicalJacobiEnergy.denseRange_polynomialEmbed (parameter q) s.val.2).induction
      ?_ (isClosed_eq (by fun_prop) (by fun_prop)) y
    rintro _ ⟨p, rfl⟩
    have h := hp s p
    simp only [polynomialEmbed, LinearMap.smul_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul] at h
    exact mul_left_cancel₀
      (Real.sqrt_pos.mpr (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property)).ne' h
  have h := congrArg (fun T : Space q →L[ℝ] ℝ ↦ T x) hLR
  simpa only [L, R, ContinuousLinearMap.comp_apply, innerSLFlip_apply_apply,
    neg_apply, lp.evalCLM, lp.evalₗ_apply, LinearMap.mkContinuous_apply,
    LinearIsometry.coe_toContinuousLinearMap] using h
end MvPolynomial.AnnularEnergy
