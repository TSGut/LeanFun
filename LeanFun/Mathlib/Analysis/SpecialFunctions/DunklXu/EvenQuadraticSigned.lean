/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.EvenQuadraticPaths

/-! # Nonnegative signed maximal-step disk matrices
The diagonal sign (-1)^a makes every maximal step nonnegative. Boundary signs
are included so that the same change applies to the Schur-complement sandwich.
Reference: finite path expansion; Dunkl--Xu Cartesian disk polynomials.
-/

@[expose] public section
open Matrix
namespace MvPolynomial

/-- The diagonal sign for the even outer degree. -/
def dunklXuInteriorSign {r : ℕ} (i : DunklXuEvenInterior r) : ℝ := (-1) ^ (i.1.1 : ℕ)

/-- Every diagonal sign squares to one. -/
theorem dunklXuInteriorSign_sq {r : ℕ} (i : DunklXuEvenInterior r) :
    dunklXuInteriorSign i * dunklXuInteriorSign i = 1 := by
  unfold dunklXuInteriorSign
  rw [← mul_pow]
  norm_num

/-- Any nonzero maximal step becomes strictly positive after the sign change. -/
theorem dunklXuEvenY2Entry_signed_pos {β : ℝ} (hβ : -1 < β) (a b c : ℕ)
    (hne : dunklXuEvenY2Entry hβ a b c (b + 1) ≠ 0) :
    0 < (-1 : ℝ) ^ a * dunklXuEvenY2Entry hβ a b c (b + 1) * (-1 : ℝ) ^ c := by
  apply lt_of_le_of_ne (dunklXuEvenY2Entry_signed_nonneg hβ a b c)
  exact Ne.symm (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hne)
    (pow_ne_zero _ (by norm_num)))

/-- The signed maximal interior matrix is entrywise nonnegative. -/
theorem dunklXuInterior_signed_maximal_nonneg {β : ℝ} (hβ : -1 < β) (u : ℝ) (r : ℕ)
    (i j : DunklXuEvenInterior r) :
    0 ≤ dunklXuInteriorSign i *
      maximalStep (dunklXuInteriorMatrix hβ u 1 r) dunklXuInteriorLevel i j * dunklXuInteriorSign j := by
  unfold maximalStep
  split_ifs with hij
  · have he : (j.1.2 : ℕ) = (i.1.2 : ℕ) + 1 := by dsimp [dunklXuInteriorLevel] at hij; omega
    dsimp [dunklXuInteriorMatrix, dunklXuInteriorSign]
    rw [he, dunklXuQuadraticMatrix_even_next_inner, one_mul]
    exact dunklXuEvenY2Entry_signed_nonneg hβ _ _ _
  · simp

/-- The signed maximal entering edge is nonnegative. -/
theorem dunklXuInterior_signed_left_nonneg {β : ℝ} (hβ : -1 < β) (u : ℝ) (r : ℕ)
    (i : DunklXuEvenInterior r) :
    0 ≤ (-1 : ℝ) ^ r *
      (if dunklXuInteriorLevel i = 1 then dunklXuInteriorLeft hβ u 1 r i else 0) *
        dunklXuInteriorSign i := by
  split_ifs with hi
  · have he : (i.1.2 : ℕ) = 1 := by dsimp [dunklXuInteriorLevel] at hi; omega
    dsimp [dunklXuInteriorLeft, dunklXuInteriorSign]
    rw [he, show 1 = 0 + 1 from rfl, dunklXuQuadraticMatrix_even_next_inner, one_mul]
    exact dunklXuEvenY2Entry_signed_nonneg hβ r 0 _
  · simp

/-- The signed maximal exiting edge is nonnegative. -/
theorem dunklXuInterior_signed_right_nonneg {β : ℝ} (hβ : -1 < β) (u : ℝ) (r : ℕ)
    (i : DunklXuEvenInterior r) :
    0 ≤ dunklXuInteriorSign i *
      (if dunklXuInteriorLevel i + 1 = r then dunklXuInteriorRight hβ u 1 r i else 0) := by
  split_ifs with hi
  · have he : r = (i.1.2 : ℕ) + 1 := by dsimp [dunklXuInteriorLevel] at hi; omega
    dsimp [dunklXuInteriorRight, dunklXuInteriorSign]
    rw [show dunklXuEvenIndex 0 r = dunklXuEvenIndex 0 ((i.1.2 : ℕ) + 1) from
      congrArg (dunklXuEvenIndex 0) he, dunklXuQuadraticMatrix_even_next_inner, one_mul]
    simpa using dunklXuEvenY2Entry_signed_nonneg hβ (i.1.1 : ℕ) (i.1.2 : ℕ) 0
  · simp

/-- Each interior edge of the explicit path is strictly positive after the sign change. -/
theorem dunklXuInterior_signed_path_pos {β : ℝ} (hβ : -1 < β) (u : ℝ)
    (r : ℕ) (hr : 2 ≤ r) (k : ℕ) (hk : k < r - 2) :
    0 < dunklXuInteriorSign (dunklXuInteriorPath r hr k) *
      maximalStep (dunklXuInteriorMatrix hβ u 1 r) dunklXuInteriorLevel
        (dunklXuInteriorPath r hr k) (dunklXuInteriorPath r hr (k + 1)) *
      dunklXuInteriorSign (dunklXuInteriorPath r hr (k + 1)) := by
  obtain ⟨ha, hb⟩ := dunklXuInteriorPath_step r hr k hk
  have hl : dunklXuInteriorLevel (dunklXuInteriorPath r hr (k + 1)) =
      dunklXuInteriorLevel (dunklXuInteriorPath r hr k) + 1 := by
    dsimp [dunklXuInteriorLevel]
    exact_mod_cast hb
  rw [maximalStep, ite_eq_left hl]
  dsimp only [dunklXuInteriorMatrix, dunklXuInteriorSign]
  rw [hb, dunklXuQuadraticMatrix_even_next_inner, one_mul]
  apply dunklXuEvenY2Entry_signed_pos
  rw [ha]
  exact (dunklXuEvenY2Entry_middle_neg hβ _ _).ne

/-- The first boundary edge of the path is strictly positive after the sign change. -/
theorem dunklXuInterior_signed_first_pos {β : ℝ} (hβ : -1 < β) (u : ℝ)
    (r : ℕ) (hr : 2 ≤ r) :
    0 < (-1 : ℝ) ^ r *
      (if dunklXuInteriorLevel (dunklXuInteriorPath r hr 0) = 1 then
        dunklXuInteriorLeft hβ u 1 r (dunklXuInteriorPath r hr 0) else 0) *
      dunklXuInteriorSign (dunklXuInteriorPath r hr 0) := by
  simp only [dunklXuInteriorLevel, dunklXuInteriorPath, Nat.zero_min, Nat.sub_zero,
    zero_add, Nat.cast_one, ite_true, dunklXuInteriorLeft, dunklXuInteriorSign]
  rw [show 1 = 0 + 1 from rfl, dunklXuQuadraticMatrix_even_next_inner, one_mul]
  apply dunklXuEvenY2Entry_signed_pos
  have h := (dunklXuEvenY2Entry_down_pos hβ (r - 2) 0).ne'
  simpa [Nat.sub_add_cancel hr] using h

/-- The final boundary edge is strictly positive, including the case r=2. -/
theorem dunklXuInterior_signed_last_pos {β : ℝ} (hβ : -1 < β) (u : ℝ)
    (r : ℕ) (hr : 2 ≤ r) :
    0 < dunklXuInteriorSign (dunklXuInteriorPath r hr (r - 2)) *
      (if dunklXuInteriorLevel (dunklXuInteriorPath r hr (r - 2)) + 1 = r then
        dunklXuInteriorRight hβ u 1 r (dunklXuInteriorPath r hr (r - 2)) else 0) := by
  have he : r - 2 + 1 + 1 = r := by omega
  simp only [dunklXuInteriorLevel, dunklXuInteriorPath, min_self, Nat.sub_self,
    dunklXuInteriorSign, pow_zero, one_mul]
  rw [ite_eq_left (by exact_mod_cast he)]
  dsimp [dunklXuInteriorRight, dunklXuInteriorPath]
  rw [show dunklXuEvenIndex 0 r = dunklXuEvenIndex 0 (r - 2 + 1 + 1) from
    congrArg (dunklXuEvenIndex 0) he.symm, dunklXuQuadraticMatrix_even_next_inner, one_mul]
  exact dunklXuEvenY2Entry_up_pos hβ 0 (r - 2 + 1)

end MvPolynomial
