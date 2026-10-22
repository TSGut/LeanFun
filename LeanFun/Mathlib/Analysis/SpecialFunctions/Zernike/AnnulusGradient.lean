/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusRadialGradient
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusBodyForcing

/-! # Cartesian gradient realization of the full annular energy space
Orthogonal synthesis of completed Cartesian gradients preserves the complete
energy norm. Together with the physical function realization, it gives a closed
function/gradient graph. Weak derivatives and zero-trace Sobolev identification
are not asserted by this completion construction alone.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology
namespace MvPolynomial.AnnularEnergy

/-- Completed Cartesian gradient sectors form an orthogonal family of isometries. -/
theorem orthogonalFamily_sectorGradient (q : Set.Ioo (0 : ℝ) 1) :
    OrthogonalFamily ℝ (RadialSpace q) (sectorGradient q) := by
  intro s r h x y
  refine (SemiclassicalJacobiEnergy.denseRange_polynomialEmbed (parameter q) s.val.2).induction
    ?_ (isClosed_eq (by fun_prop) continuous_const) x
  rintro _ ⟨p, rfl⟩
  refine (SemiclassicalJacobiEnergy.denseRange_polynomialEmbed (parameter q) r.val.2).induction
    ?_ (isClosed_eq (by fun_prop) continuous_const) y
  rintro _ ⟨z, rfl⟩
  have he : inner ℝ (radialPolynomialGradient q s p) (radialPolynomialGradient q r z) = 0 := by
    change inner ℝ (polynomialGradient q _) (polynomialGradient q _) = 0
    rw [inner_polynomialGradient]
    apply integralInner_annulusDirichlet_gradient_eq_zero q.property
    by_contra! hh
    exact h (Subtype.ext (Prod.ext hh.1 hh.2))
  rw [sectorGradient_polynomialEmbed, sectorGradient_polynomialEmbed]
  simp [normalizedPolynomialGradient, real_inner_smul_left, inner_smul_right, he]

/-- The full annular energy norm is the norm of its physical Cartesian gradient classes. -/
def gradientL2 (q : Set.Ioo (0 : ℝ) 1) : Space q →ₗᵢ[ℝ] GradientL2 q :=
  (orthogonalFamily_sectorGradient q).linearIsometry

/-- Cartesian gradients are the unconditionally convergent sum of their normalized sectors. -/
theorem hasSum_gradientL2 (q : Set.Ioo (0 : ℝ) 1) (x : Space q) :
    HasSum (fun s ↦ sectorGradient q s (x s)) (gradientL2 q x) :=
  (orthogonalFamily_sectorGradient q).hasSum_linearIsometry x

/-- The gradient realization preserves the full energy inner product. -/
theorem inner_gradientL2 (q : Set.Ioo (0 : ℝ) 1) (x y : Space q) :
    inner ℝ (gradientL2 q x) (gradientL2 q y) = inner ℝ x y :=
  (gradientL2 q).inner_map_map x y

/-- No completed energy vector is lost in the Cartesian gradient realization. -/
theorem gradientL2_injective (q : Set.Ioo (0 : ℝ) 1) :
    Function.Injective (gradientL2 q) := (gradientL2 q).injective

/-- The completed Cartesian gradient space is closed in the physical vector-field L² space. -/
theorem isClosed_range_gradientL2 (q : Set.Ioo (0 : ℝ) 1) :
    IsClosed (Set.range (gradientL2 q)) :=
  (gradientL2 q).isometry.isClosedEmbedding.isClosed_range

/-- A single normalized sector has the prescribed completed gradient. -/
theorem gradientL2_sectorEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (x : RadialSpace q s) :
    gradientL2 q (sectorEmbed q s x) = sectorGradient q s x := by
  classical
  exact (orthogonalFamily_sectorGradient q).linearIsometry_apply_single x

/-- Physical polynomial energy vectors realize precisely their Cartesian polynomial gradients. -/
theorem gradientL2_polynomialEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (p : Polynomial ℝ) :
    gradientL2 q (polynomialEmbed q s p) =
      polynomialGradient q (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p) := by
  have hs : Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) ≠ 0 :=
    (Real.sqrt_pos.mpr (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property)).ne'
  simp only [polynomialEmbed, LinearMap.smul_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, map_smul, gradientL2_sectorEmbed, sectorGradient_polynomialEmbed,
    normalizedPolynomialGradient, smul_smul, mul_inv_cancel₀ hs, one_smul]
  rfl

/-- The simultaneous function and gradient realization is an isometry for the product max norm. -/
def functionGradient (q : Set.Ioo (0 : ℝ) 1) :
    Space q →ₗᵢ[ℝ] PhysicalL2 q × GradientL2 q where
  __ := (physicalL2 q).toLinearMap.prod (gradientL2 q).toLinearMap
  norm_map' x := by
    change max ‖physicalL2 q x‖ ‖gradientL2 q x‖ = ‖x‖
    rw [LinearIsometry.norm_map, max_eq_right (norm_physicalL2_le q x)]

/-- The simultaneous physical function/gradient graph is closed. -/
theorem isClosed_range_functionGradient (q : Set.Ioo (0 : ℝ) 1) :
    IsClosed (Set.range (functionGradient q)) :=
  (functionGradient q).isometry.isClosedEmbedding.isClosed_range

/-- The completed physical body-force equation is a pairing of physical gradient classes. -/
theorem gradient_body_solution_weak (q : Set.Ioo (0 : ℝ) 1) (g : PhysicalL2 q) (z : Space q) :
    inner ℝ (gradientL2 q (solution q (bodyLoad q g))) (gradientL2 q z) =
      inner ℝ g (physicalL2 q z) := by
  rw [inner_gradientL2]
  exact body_solution_weak q g z

/-- The actual finite reconstructions have precisely the energy error in Cartesian gradient L². -/
theorem norm_gradientL2_error (q : Set.Ioo (0 : ℝ) 1) (c : Finset Sector × ℕ)
    (ℓ : Space q →L[ℝ] ℝ) :
    ‖gradientL2 q (solution q ℓ) - gradientL2 q (finiteSolve q c ℓ)‖ =
      ‖solution q ℓ - finiteSolve q c ℓ‖ := by
  rw [← map_sub, LinearIsometry.norm_map]

/-- Common angular and radial cutoffs converge simultaneously as functions and Cartesian gradients. -/
theorem tendsto_functionGradient_finiteSolve (q : Set.Ioo (0 : ℝ) 1)
    (ℓ : Space q →L[ℝ] ℝ) :
    Tendsto (fun N ↦ functionGradient q (finiteSolve q (frequencyCutoff N, N) ℓ)) atTop
      (𝓝 (functionGradient q (solution q ℓ))) :=
  (functionGradient q).continuous.tendsto _ |>.comp (tendsto_finiteSolve_frequencyCutoff q ℓ)

end MvPolynomial.AnnularEnergy
