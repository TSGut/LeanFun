/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.EvenQuadraticSigned
public import LeanFun.Mathlib.Analysis.Matrix.InversePathCoefficient

/-! # Noncancelling elimination coefficients in every even disk degree
The first possible boundary-to-boundary path coefficient is nonzero for every
r>=2. Its proof uses strict signs and an explicit path, not finite experiments.
Reference: Schur complements and finite Neumann expansion; Dunkl--Xu disk bases.
-/

@[expose] public section
open Matrix Filter
open scoped Topology
namespace MvPolynomial

/-- The boundary-to-boundary pairing of an interior matrix. -/
noncomputable def dunklXuInteriorFunctional {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ) :
    Matrix (DunklXuEvenInterior r) (DunklXuEvenInterior r) ℝ →ₗ[ℝ] ℝ where
  toFun M := ∑ i, ∑ j, dunklXuInteriorLeft hβ u v r i * M i j * dunklXuInteriorRight hβ u v r j
  map_add' M N := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' a M := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

/-- The first allowed elimination coefficient is nonzero in every degree. -/
theorem dunklXuInterior_first_coefficient_ne_zero {β : ℝ} (hβ : -1 < β) (u : ℝ)
    (r : ℕ) (hr : 2 ≤ r) :
    dunklXuInteriorFunctional hβ u 1 r (dunklXuInteriorMatrix hβ u 1 r ^ (r - 2)) ≠ 0 := by
  let K := maximalStep (dunklXuInteriorMatrix hβ u 1 r) dunklXuInteriorLevel
  let F : DunklXuEvenInterior r → ℝ := fun i ↦
    if dunklXuInteriorLevel i = 1 then dunklXuInteriorLeft hβ u 1 r i else 0
  let G : DunklXuEvenInterior r → ℝ := fun i ↦
    if dunklXuInteriorLevel i + 1 = r then dunklXuInteriorRight hβ u 1 r i else 0
  have hp := sum_mul_pow_mul_pos_of_positive_path
    (Matrix.of (fun i j ↦ dunklXuInteriorSign i * K i j * dunklXuInteriorSign j))
    (fun i ↦ (-1 : ℝ) ^ r * F i * dunklXuInteriorSign i)
    (fun j ↦ dunklXuInteriorSign j * G j * 1)
    (dunklXuInterior_signed_maximal_nonneg hβ u r)
    (dunklXuInterior_signed_left_nonneg hβ u r)
    (fun i ↦ by simpa only [mul_one] using dunklXuInterior_signed_right_nonneg hβ u r i)
    (r - 2) (dunklXuInteriorPath r hr)
    (dunklXuInterior_signed_first_pos hβ u r hr)
    (by simpa only [mul_one] using dunklXuInterior_signed_last_pos hβ u r hr)
    (dunklXuInterior_signed_path_pos hβ u r hr)
  rw [sum_mul_pow_mul_sign_conjugate K F G dunklXuInteriorSign ((-1 : ℝ) ^ r) 1
    dunklXuInteriorSign_sq, mul_one] at hp
  have he := sum_mul_pow_mul_eq_maximalStep (dunklXuInteriorMatrix hβ u 1 r)
    (dunklXuInteriorLeft hβ u 1 r) (dunklXuInteriorRight hβ u 1 r)
    dunklXuInteriorLevel 0 r (dunklXuInteriorMatrix_level_band hβ u 1 r)
    (dunklXuInteriorLeft_level_band hβ u 1 r) (dunklXuInteriorRight_level_band hβ u 1 r)
    (r - 2) (by omega)
  change (∑ i, ∑ j, dunklXuInteriorLeft hβ u 1 r i *
    (dunklXuInteriorMatrix hβ u 1 r ^ (r - 2)) i j * dunklXuInteriorRight hβ u 1 r j) =
      ∑ i, ∑ j, F i * (K ^ (r - 2)) i j * G j at he
  rw [← he] at hp
  intro hz
  change (∑ i, ∑ j, dunklXuInteriorLeft hβ u 1 r i *
    (dunklXuInteriorMatrix hβ u 1 r ^ (r - 2)) i j * dunklXuInteriorRight hβ u 1 r j) = 0 at hz
  rw [hz, mul_zero] at hp
  exact lt_irrefl 0 hp

/-- The actual finite inverse sandwich is nonzero for all sufficiently small
nonzero perturbations, at every requested degree. -/
theorem eventually_dunklXuInterior_inverse_ne_zero {β : ℝ} (hβ : -1 < β) (u : ℝ)
    (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      dunklXuInteriorFunctional hβ u 1 r ((1 + t • dunklXuInteriorMatrix hβ u 1 r)⁻¹) ≠ 0 := by
  apply eventually_apply_inv_one_add_smul_ne_zero _ _ (r - 2)
  · intro q hq
    exact dunklXuInterior_sandwich_eq_zero hβ u 1 r q (by omega)
  · exact dunklXuInterior_first_coefficient_ne_zero hβ u r hr

end MvPolynomial
