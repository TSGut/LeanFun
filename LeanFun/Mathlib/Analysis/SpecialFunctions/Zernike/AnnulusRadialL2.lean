/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusPoincare
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusEnergySpace
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.L2
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # Physical L² realizations of completed annular sectors
The uniform polynomial Poincaré estimate extends each radial energy completion
to physical annular L² functions. Square-integrable body forces consequently
act continuously on each sector. Faithfulness and the full Sobolev identification
are separate from this bounded extension.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Filter
open scoped Topology
/-- Reparametrizing polynomial energy vectors preserves density in the completion. -/
theorem Polynomial.SemiclassicalJacobiEnergy.denseRange_polynomialEmbed
    (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    DenseRange (SemiclassicalJacobiEnergy.polynomialEmbed t γ) := by
  have hr : Set.range (SemiclassicalJacobiEnergy.polynomialEmbed t γ) =
      Set.range (SemiclassicalJacobiEnergy.embed t γ) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(SemiclassicalJacobiEnergy.polynomialEquiv t γ).symm p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨SemiclassicalJacobiEnergy.polynomialEquiv t γ p, by
        simp [SemiclassicalJacobiEnergy.polynomialEmbed]⟩
  intro x
  rw [hr]
  exact SemiclassicalJacobiEnergy.denseRange_embed t γ x

namespace MvPolynomial.AnnularEnergy

/-- Physical L² classes on the annulus, with its unweighted area measure. -/
abbrev PhysicalL2 (q : Set.Ioo (0 : ℝ) 1) := Lp ℝ 2 (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0)

/-- Finite moments for the physical area measure. -/
theorem physicalMeasure_moments (q : Set.Ioo (0 : ℝ) 1) :
    HasFiniteMoments (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) :=
  hasFiniteMoments_zernikeAnnulusMeasure q.property (by norm_num) (by norm_num)

/-- A physical boundary-weighted sector polynomial, regarded as an L² class. -/
def radialPolynomialL2 (q : Set.Ioo (0 : ℝ) 1) (s : Sector) : Polynomial ℝ →ₗ[ℝ] PhysicalL2 q :=
  (MvPolynomial.polynomialToL2 (physicalMeasure_moments q)).comp
    (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2)

/-- Poincaré bounds the physical L² norm by the correctly scaled radial energy norm. -/
theorem norm_radialPolynomialL2_le (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (p : Polynomial ℝ) :
    ‖radialPolynomialL2 q s p‖ ≤ Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) *
      ‖SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p‖ := by
  have h := integralInner_annulus_boundary_le_neg_laplacian q.property
    (annulusLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p)
  change integralInner _ (IntegrablePair.of _ (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p) (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p) (h := (hasFiniteMoments_zernikeAnnulusMeasure q.property (by norm_num) (by norm_num)).integrable_mul _ _)) ≤
    -integralInner _ (IntegrablePair.of _ (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p)) (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p) (h := (hasFiniteMoments_zernikeAnnulusMeasure q.property (by norm_num) (by norm_num)).integrable_mul _ _)) at h
  rw [neg_integralInner_annulusDirichletLaplacian q.property] at h
  have he : ‖radialPolynomialL2 q s p‖^2 =
      integralInner (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p) (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p) (h := (hasFiniteMoments_zernikeAnnulusMeasure q.property (by norm_num) (by norm_num)).integrable_mul _ _)) := by
    rw [← real_inner_self_eq_norm_sq]
    exact MvPolynomial.inner_polynomialToL2 (physicalMeasure_moments q) _ _
  have hs := Real.sq_sqrt (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property).le
  rw [real_inner_self_eq_norm_sq] at h
  change _ ≤ annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 *
    ‖SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p‖^2 at h
  have hn : 0 ≤ Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) *
      ‖SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p‖ := by positivity
  nlinarith [norm_nonneg (radialPolynomialL2 q s p)]

/-- The physical L² realization of one completed radial sector. -/
def radialL2 (q : Set.Ioo (0 : ℝ) 1) (s : Sector) : RadialSpace q s →L[ℝ] PhysicalL2 q :=
  (radialPolynomialL2 q s).extendOfNorm
    (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2)

/-- The extension retains the prescribed boundary-weighted polynomial values. -/
theorem radialL2_polynomialEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (p : Polynomial ℝ) :
    radialL2 q s (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p) =
      radialPolynomialL2 q s p := by
  apply LinearMap.extendOfNorm_eq
  · exact SemiclassicalJacobiEnergy.denseRange_polynomialEmbed _ _
  · exact ⟨_, norm_radialPolynomialL2_le q s⟩

/-- Poincaré persists on the completed radial energy space. -/
theorem norm_radialL2_le (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (x : RadialSpace q s) :
    ‖radialL2 q s x‖ ≤ Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le
    (SemiclassicalJacobiEnergy.denseRange_polynomialEmbed _ _) _ (norm_radialPolynomialL2_le q s) x

/-- Ordinary physical L² body forcing defines a continuous load on a completed radial sector. -/
def radialBodyLoad (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (g : PhysicalL2 q) :
    RadialSpace q s →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (PhysicalL2 q) g).comp (radialL2 q s)

/-- The body load is the physical L² pairing with the realized solution. -/
theorem radialBodyLoad_apply (q : Set.Ioo (0 : ℝ) 1) (s : Sector)
    (g : PhysicalL2 q) (x : RadialSpace q s) :
    radialBodyLoad q s g x = inner ℝ g (radialL2 q s x) := rfl

/-- The body-load bound includes exactly the physical angular scale. -/
theorem norm_radialBodyLoad_le (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (g : PhysicalL2 q) :
    ‖radialBodyLoad q s g‖ ≤ ‖g‖ * Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [radialBodyLoad_apply]
  exact (norm_inner_le_norm g _).trans ((mul_le_mul_of_nonneg_left
    (norm_radialL2_le q s x) (norm_nonneg g)).trans_eq (mul_assoc _ _ _).symm)

/-- On polynomial trials, the body load is the usual physical integral. -/
theorem radialBodyLoad_polynomialEmbed (q : Set.Ioo (0 : ℝ) 1) (s : Sector)
    (g : PhysicalL2 q) (p : Polynomial ℝ) :
    radialBodyLoad q s g (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p) =
      ∫ v, g v * eval v (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p)
        ∂zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0 := by
  rw [radialBodyLoad_apply, radialL2_polynomialEmbed, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MvPolynomial.coe_polynomialToL2 (physicalMeasure_moments q)
    (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p)] with v hv
  change inner ℝ (g v) ((MvPolynomial.polynomialToL2 (physicalMeasure_moments q)
    (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p)) v) = _
  simp [hv, mul_comm]

/-- The physical Poisson load expressed in the solver's unscaled radial energy coordinates. -/
def radialPoissonLoad (q : Set.Ioo (0 : ℝ) 1) (s : Sector) (g : PhysicalL2 q) :
    RadialSpace q s →L[ℝ] ℝ :=
  (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2)⁻¹ • radialBodyLoad q s g

/-- The radial solution satisfies the correctly scaled physical weak equation in its sector. -/
theorem radialPoisson_solution_weak (q : Set.Ioo (0 : ℝ) 1) (s : Sector)
    (g : PhysicalL2 q) (z : RadialSpace q s) :
    annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 * inner ℝ
      (SemiclassicalJacobiEnergy.solution (parameter q) s.val.2 (radialPoissonLoad q s g)) z =
      inner ℝ g (radialL2 q s z) := by
  rw [SemiclassicalJacobiEnergy.solution_weak]
  change annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 *
    ((annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2)⁻¹ * inner ℝ g (radialL2 q s z)) = _
  rw [← mul_assoc, mul_inv_cancel₀
    (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property).ne', one_mul]

/-- The existing radial coefficient solves converge in physical annular L². -/
theorem tendsto_radialL2_coefficients (q : Set.Ioo (0 : ℝ) 1) (s : Sector)
    (ℓ : RadialSpace q s →L[ℝ] ℝ) :
    Tendsto (fun N ↦ radialL2 q s
      (SemiclassicalJacobiEnergy.trialEmbed (parameter q) s.val.2 N
        (SemiclassicalJacobiEnergy.coefficients (parameter q) s.val.2 N ℓ))) atTop
      (𝓝 (radialL2 q s (SemiclassicalJacobiEnergy.solution (parameter q) s.val.2 ℓ))) :=
  (radialL2 q s).continuous.tendsto _ |>.comp
    (SemiclassicalJacobiEnergy.tendsto_trialEmbed_coefficients (parameter q) s.val.2 ℓ)

end MvPolynomial.AnnularEnergy
