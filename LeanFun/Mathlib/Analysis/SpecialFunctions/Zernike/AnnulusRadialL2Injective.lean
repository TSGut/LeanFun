/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusRadialL2

/-! # Faithfulness of the physical radial L² realization
Polynomial Laplacians detect the energy pairing with a dense family of tests.
Consequently the completed L² realization has zero kernel, without first
identifying weak gradients or a Sobolev space.
Reference: the annular Dirichlet form in Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open Polynomial MeasureTheory
namespace MvPolynomial.AnnularEnergy

/-- Completed sector energy can be tested against physical polynomial Laplacians. -/
theorem inner_radialL2_polynomialLaplacian (q : Set.Ioo (0 : ℝ) 1) (s : Sector)
    (x : RadialSpace q s) (p : Polynomial ℝ) :
    annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 * inner ℝ x
      (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p) =
    -inner ℝ (radialL2 q s x)
      (MvPolynomial.polynomialToL2 (physicalMeasure_moments q)
        (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p))) := by
  refine (SemiclassicalJacobiEnergy.denseRange_polynomialEmbed (parameter q) s.val.2).induction
    ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
  rintro _ ⟨z, rfl⟩
  rw [radialL2_polynomialEmbed, real_inner_comm]
  change annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 * inner ℝ
    (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 p)
    (SemiclassicalJacobiEnergy.polynomialEmbed (parameter q) s.val.2 z) =
      -inner ℝ (MvPolynomial.polynomialToL2 (physicalMeasure_moments q) _)
        (MvPolynomial.polynomialToL2 (physicalMeasure_moments q) _)
  rw [MvPolynomial.inner_polynomialToL2]
  change _ = -integralInner (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0) (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 z) (diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p)) (h := (hasFiniteMoments_zernikeAnnulusMeasure q.property (by norm_num) (by norm_num)).integrable_mul _ _))
  rw [integralInner_comm]
  exact (neg_integralInner_annulusDirichletLaplacian q.property s.val.1 s.val.2 p z).symm

/-- A radial energy vector whose physical L² class vanishes is zero. -/
theorem radialL2_injective (q : Set.Ioo (0 : ℝ) 1) (s : Sector) :
    Function.Injective (radialL2 q s) := by
  apply (LinearMap.ker_eq_bot (f := (radialL2 q s).toLinearMap)).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply ext_inner_right ℝ
  intro y
  simp only [inner_zero_left]
  refine (SemiclassicalJacobiEnergy.denseRange_polynomialEmbed (parameter q) s.val.2).induction
    ?_ (isClosed_eq (by fun_prop) continuous_const) y
  rintro _ ⟨p, rfl⟩
  have he := inner_radialL2_polynomialLaplacian q s x p
  change radialL2 q s x = 0 at hx
  rw [hx, inner_zero_left, neg_zero] at he
  exact (mul_eq_zero.mp he).resolve_left
    (annulusEnergyScale_pos q.property s.val.1 s.val.2 s.property).ne'

end MvPolynomial.AnnularEnergy
