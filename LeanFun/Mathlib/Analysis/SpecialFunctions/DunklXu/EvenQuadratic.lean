/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticMatrix

/-! # Even-even disk multiplication steps
The pair (a,b) means the existing index (n,k)=(2a+2b,2b).
This is a reindexing of the existing normalized disk basis, not a new family.
Reference: Dunkl--Xu, Cartesian disk construction.
-/

@[expose] public section
namespace MvPolynomial

/-- Index embedding for the even-even Cartesian disk sector. -/
def dunklXuEvenIndex (a b : ℕ) : Σ n : ℕ, Fin (n + 1) :=
  ⟨2 * a + 2 * b, ⟨2 * b, by omega⟩⟩

/-- Normalized y² entry between existing even-even basis elements. -/
noncomputable def dunklXuEvenY2Entry {β : ℝ} (hβ : -1 < β) (a b c d : ℕ) : ℝ :=
  dunklXuQuadraticMatrix hβ 0 1 (dunklXuEvenIndex a b) (dunklXuEvenIndex c d)

/-- At a maximal inner step, the quadratic perturbation is exactly c times y²,
independently of the outer-coordinate coefficient b. -/
theorem dunklXuQuadraticMatrix_even_next_inner {β : ℝ} (hβ : -1 < β)
    (u v : ℝ) (a b c : ℕ) :
    dunklXuQuadraticMatrix hβ u v (dunklXuEvenIndex a b) (dunklXuEvenIndex c (b + 1)) =
      v * dunklXuEvenY2Entry hβ a b c (b + 1) := by
  rw [dunklXuEvenY2Entry, dunklXuQuadraticMatrix_of_inner_ne hβ u v _ _
    (by simp only [dunklXuEvenIndex]; omega),
    dunklXuQuadraticMatrix_of_inner_ne hβ 0 1 _ _
      (by simp only [dunklXuEvenIndex]; omega)]
  ring

/-- The top outer-degree maximal inner step is strictly positive. -/
theorem dunklXuEvenY2Entry_up_pos {β : ℝ} (hβ : -1 < β) (a b : ℕ) :
    0 < dunklXuEvenY2Entry hβ a b a (b + 1) := by
  rw [dunklXuEvenY2Entry, dunklXuQuadraticMatrix_of_inner_ne hβ 0 1 _ _
    (by simp only [dunklXuEvenIndex]; omega)]
  simp only [one_mul, dunklXuEvenIndex]
  apply mul_pos (mul_pos (inv_pos.mpr (dunklXuNorm_pos hβ _ _))
    (inv_pos.mpr (dunklXuNorm_pos hβ _ _)))
  simpa only [Nat.mul_add, Nat.mul_one] using
    integralInner_y_sq_dunklXuDisk_up_pos hβ (2 * a) (2 * b)

/-- The middle outer-degree maximal inner step is strictly negative. -/
theorem dunklXuEvenY2Entry_middle_neg {β : ℝ} (hβ : -1 < β) (a b : ℕ) :
    dunklXuEvenY2Entry hβ (a + 1) b a (b + 1) < 0 := by
  rw [dunklXuEvenY2Entry, dunklXuQuadraticMatrix_of_inner_ne hβ 0 1 _ _
    (by simp only [dunklXuEvenIndex]; omega)]
  simp only [one_mul, dunklXuEvenIndex]
  apply mul_neg_of_pos_of_neg (mul_pos (inv_pos.mpr (dunklXuNorm_pos hβ _ _))
    (inv_pos.mpr (dunklXuNorm_pos hβ _ _)))
  simpa only [Nat.mul_add, Nat.mul_one] using
    integralInner_y_sq_dunklXuDisk_same_degree_neg hβ (2 * a) (2 * b)

/-- The bottom outer-degree maximal inner step is strictly positive. -/
theorem dunklXuEvenY2Entry_down_pos {β : ℝ} (hβ : -1 < β) (a b : ℕ) :
    0 < dunklXuEvenY2Entry hβ (a + 2) b a (b + 1) := by
  rw [dunklXuEvenY2Entry, dunklXuQuadraticMatrix_of_inner_ne hβ 0 1 _ _
    (by simp only [dunklXuEvenIndex]; omega)]
  simp only [one_mul, dunklXuEvenIndex]
  apply mul_pos (mul_pos (inv_pos.mpr (dunklXuNorm_pos hβ _ _))
    (inv_pos.mpr (dunklXuNorm_pos hβ _ _)))
  simpa only [Nat.mul_add, Nat.mul_one, show 2 * 2 = 4 from rfl] using
    integralInner_y_sq_dunklXuDisk_down_pos hβ (2 * a) (2 * b)

/-- No other outer degrees occur at an upward inner step. -/
theorem dunklXuEvenY2Entry_eq_zero {β : ℝ} (hβ : -1 < β) (a b c : ℕ)
    (h₀ : a ≠ c) (h₁ : a ≠ c + 1) (h₂ : a ≠ c + 2) :
    dunklXuEvenY2Entry hβ a b c (b + 1) = 0 := by
  rw [dunklXuEvenY2Entry, dunklXuQuadraticMatrix_of_inner_ne hβ 0 1 _ _
    (by simp only [dunklXuEvenIndex]; omega)]
  simp only [dunklXuEvenIndex, Nat.mul_add, Nat.mul_one]
  rw [integralInner_y_sq_dunklXuDisk_inner_add_two_eq_zero hβ (2 * a) (2 * c) (2 * b)
    (by omega) (by omega) (by omega), mul_zero]

/-- Diagonal sign changes remove every sign of a maximal inner step. -/
theorem dunklXuEvenY2Entry_signed_nonneg {β : ℝ} (hβ : -1 < β) (a b c : ℕ) :
    0 ≤ (-1 : ℝ) ^ a * dunklXuEvenY2Entry hβ a b c (b + 1) * (-1 : ℝ) ^ c := by
  have hs : (-1 : ℝ) ^ c * (-1 : ℝ) ^ c = 1 := by rw [← mul_pow]; norm_num
  by_cases h₀ : a = c
  · subst a
    have hp := (dunklXuEvenY2Entry_up_pos hβ c b).le
    nlinarith [hs]
  by_cases h₁ : a = c + 1
  · subst a
    rw [pow_add, pow_one]
    have hp := (dunklXuEvenY2Entry_middle_neg hβ c b).le
    nlinarith [hs]
  by_cases h₂ : a = c + 2
  · subst a
    rw [pow_add]
    norm_num only [neg_one_sq, mul_one]
    have hp := (dunklXuEvenY2Entry_down_pos hβ c b).le
    nlinarith [hs]
  rw [dunklXuEvenY2Entry_eq_zero hβ a b c h₀ h₁ h₂]
  simp

end MvPolynomial
