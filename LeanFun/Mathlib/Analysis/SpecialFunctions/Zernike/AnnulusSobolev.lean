/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusDensity
/-! # The annular zero-boundary Sobolev problem

The completed polynomial energy space is isometrically identified with the
closure of compactly supported smooth function/gradient pairs. The existing
Riesz solution and finite angular/radial solves therefore give the standard
weak Dirichlet problem and convergence in the function/gradient norm.
Reference: Evans, *Partial Differential Equations*, Chapter 5; the annular
spectral discretization is that of Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MvPolynomial.AnnularEnergy

/-- The physical energy graph as an element of the zero-boundary Sobolev graph. -/
def dirichletEmbedding (q : Ioo (0 : ℝ) 1) :
    Space q →ₗᵢ[ℝ] DirichletSpace.Space (domain q) where
  __ := ((areaGraphEquiv q).toLinearMap.comp (functionGradient q).toLinearMap).codRestrict
    (DirichletSpace.graph (domain q)) (functionGradient_mem_dirichlet q)
  norm_map' x := by
    change ‖areaGraphEquiv q (functionGradient q x)‖ = ‖x‖
    simp

/-- Polynomial and smooth-test density make the energy embedding onto the Sobolev graph. -/
theorem dirichletEmbedding_surjective (q : Ioo (0 : ℝ) 1) :
    Function.Surjective (dirichletEmbedding q) := by
  let F := (areaGraphEquiv q).toLinearIsometry.comp (functionGradient q)
  have hc : IsClosed (Set.range F) := F.isometry.isClosedEmbedding.isClosed_range
  have hs : (DirichletSpace.graph (domain q) : Set _) ⊆ Set.range F := by
    apply closure_minimal _ hc
    rintro _ ⟨φ,rfl⟩
    obtain ⟨x,hx⟩ := physicalTestGraph_mem_range q φ
    refine ⟨x, ?_⟩
    change areaGraphEquiv q (functionGradient q x) = DirichletSpace.testGraph (domain q) φ
    rw [hx,areaGraphEquiv_testGraph]
  intro y
  obtain ⟨x,hx⟩ := hs y.property
  exact ⟨x,Subtype.ext hx⟩

/-- The isometric identification of the energy completion with the annular H₀¹ graph. -/
def dirichletEquiv (q : Ioo (0 : ℝ) 1) :
    Space q ≃ₗᵢ[ℝ] DirichletSpace.Space (domain q) :=
  LinearIsometryEquiv.ofSurjective (dirichletEmbedding q) (dirichletEmbedding_surjective q)

/-- The identification retains the actual physical function and Cartesian gradient. -/
theorem coe_dirichletEquiv (q : Ioo (0 : ℝ) 1) (x : Space q) :
    ((dirichletEquiv q x : DirichletSpace.Space (domain q)) :
      DirichletSpace.FunctionL2 (domain q) × DirichletSpace.GradientL2 (domain q)) =
      areaGraphEquiv q (functionGradient q x) := rfl

/-- The Cartesian gradient inner product is the completed energy pairing. -/
theorem inner_dirichletEquiv_gradient (q : Ioo (0 : ℝ) 1) (x y : Space q) :
    inner ℝ (dirichletEquiv q x).val.2 (dirichletEquiv q y).val.2 = inner ℝ x y := by
  rw [coe_dirichletEquiv,coe_dirichletEquiv]
  change inner ℝ (L2.graphMeasureCongr 2 (zernikeAnnulusMeasure_zero_zero_eq_volume q.property) (functionGradient q x)).2
    (L2.graphMeasureCongr 2 (zernikeAnnulusMeasure_zero_zero_eq_volume q.property) (functionGradient q y)).2 = _
  rw [L2.graphMeasureCongr_inner_snd]
  exact inner_gradientL2 q x y

/-- The weak zero-boundary solution for a continuous Sobolev load. -/
def dirichletSolution (q : Ioo (0 : ℝ) 1)
    (L : DirichletSpace.Space (domain q) →L[ℝ] ℝ) : DirichletSpace.Space (domain q) :=
  dirichletEquiv q (solution q (L.comp (dirichletEquiv q).toLinearIsometry.toContinuousLinearMap))

/-- The transported solution satisfies the weak Dirichlet equation against every Sobolev test. -/
theorem dirichletSolution_weak (q : Ioo (0 : ℝ) 1)
    (L : DirichletSpace.Space (domain q) →L[ℝ] ℝ) (v : DirichletSpace.Space (domain q)) :
    inner ℝ (dirichletSolution q L).val.2 v.val.2 = L v := by
  obtain ⟨z,rfl⟩ := (dirichletEquiv q).surjective v
  let ℓ := L.comp (dirichletEquiv q).toLinearIsometry.toContinuousLinearMap
  have h := (inner_dirichletEquiv_gradient q (solution q ℓ) z).trans (solution_weak q ℓ z)
  simpa only [dirichletSolution, ℓ, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry] using h

/-- Every continuous Sobolev load has exactly one weak Dirichlet solution. -/
theorem existsUnique_dirichletSolution (q : Ioo (0 : ℝ) 1)
    (L : DirichletSpace.Space (domain q) →L[ℝ] ℝ) :
    ∃! u : DirichletSpace.Space (domain q), ∀ v : DirichletSpace.Space (domain q),
      inner ℝ u.val.2 v.val.2 = L v := by
  refine ⟨dirichletSolution q L,dirichletSolution_weak q L,?_⟩
  intro u hu
  obtain ⟨x,rfl⟩ := (dirichletEquiv q).surjective u
  unfold dirichletSolution
  apply congrArg (dirichletEquiv q)
  apply ext_inner_right ℝ
  intro z
  rw [solution_weak]
  change inner ℝ x z = L (dirichletEquiv q z)
  simpa only [inner_dirichletEquiv_gradient] using hu (dirichletEquiv q z)

/-- The existing finite angular and radial solves converge in the Sobolev graph norm. -/
theorem tendsto_dirichlet_finiteSolve (q : Ioo (0 : ℝ) 1)
    (L : DirichletSpace.Space (domain q) →L[ℝ] ℝ) :
    Tendsto (fun N ↦ dirichletEquiv q (finiteSolve q (frequencyCutoff N,N)
      (L.comp (dirichletEquiv q).toLinearIsometry.toContinuousLinearMap))) atTop
      (𝓝 (dirichletSolution q L)) :=
  (dirichletEquiv q).continuous.tendsto _ |>.comp (tendsto_finiteSolve_frequencyCutoff q _)

/-- An ordinary area-L² body force acts on the Sobolev function component. -/
def dirichletBodyLoad (q : Ioo (0 : ℝ) 1) (g : DirichletSpace.FunctionL2 (domain q)) :
    DirichletSpace.Space (domain q) →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (DirichletSpace.FunctionL2 (domain q)) g).comp
    ((ContinuousLinearMap.fst ℝ (DirichletSpace.FunctionL2 (domain q))
      (DirichletSpace.GradientL2 (domain q))).comp (DirichletSpace.graph (domain q)).subtypeL)

/-- The body load is precisely its area-L² pairing with the function component. -/
theorem dirichletBodyLoad_apply (q : Ioo (0 : ℝ) 1)
    (g : DirichletSpace.FunctionL2 (domain q)) (v : DirichletSpace.Space (domain q)) :
    dirichletBodyLoad q g v = inner ℝ g v.val.1 := rfl

/-- An area-L² body force gives the standard weak Poisson equation. -/
theorem dirichletBodySolution_weak (q : Ioo (0 : ℝ) 1)
    (g : DirichletSpace.FunctionL2 (domain q)) (v : DirichletSpace.Space (domain q)) :
    inner ℝ (dirichletSolution q (dirichletBodyLoad q g)).val.2 v.val.2 = inner ℝ g v.val.1 :=
  dirichletSolution_weak q (dirichletBodyLoad q g) v

/-- The ordinary area body load pulls back to the existing physical energy body load. -/
theorem dirichletBodyLoad_transport (q : Ioo (0 : ℝ) 1) (g : PhysicalL2 q) :
    (dirichletBodyLoad q (areaGraphEquiv q (g,0)).1).comp
      (dirichletEquiv q).toLinearIsometry.toContinuousLinearMap = bodyLoad q g := by
  apply ContinuousLinearMap.ext
  intro x
  change inner ℝ (areaGraphEquiv q (g,0)).1 (dirichletEquiv q x).val.1 = inner ℝ g (physicalL2 q x)
  rw [coe_dirichletEquiv]
  exact L2.graphMeasureCongr_inner_fst 2 _ (g,0) (functionGradient q x)
end MvPolynomial.AnnularEnergy
