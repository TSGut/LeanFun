/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Matrix powers at the maximal level increase

If one multiplication raises an integer level by at most one, an n-step
contribution that raises it by n must raise it at every step. Terms that
preserve the level cannot affect this first possible coefficient.
Reference: the finite matrix path expansion; used with Koornwinder inner indices.
-/

@[expose] public section
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Retain only entries that raise the column level by exactly one. -/
def maximalStep (A : Matrix ι ι ℝ) (level : ι → ℤ) : Matrix ι ι ℝ :=
  fun i j => if level j = level i+1 then A i j else 0

/-- An n-fold product cannot raise the level by more than n. -/
theorem pow_apply_eq_zero_of_level_gap (A : Matrix ι ι ℝ) (level : ι → ℤ)
    (hA : ∀ i j, level i+1 < level j → A i j = 0)
    (n : ℕ) (i j : ι) (hgap : level i+n < level j) : (A^n) i j = 0 := by
  induction n generalizing i j with
  | zero =>
    have hne : i ≠ j := by intro h; subst j; omega
    simp [hne]
  | succ n ih =>
    rw [pow_succ', mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : level i+1 < level k
    · rw [hA i k hk, zero_mul]
    · rw [ih k j (by omega), mul_zero]

/-- At the maximal possible level gap, only maximal-step entries contribute. -/
theorem pow_apply_eq_maximalStep (A : Matrix ι ι ℝ) (level : ι → ℤ)
    (hA : ∀ i j, level i+1 < level j → A i j = 0)
    (n : ℕ) (i j : ι) (hgap : level j = level i+n) :
    (A^n) i j = ((maximalStep A level)^n) i j := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_apply, mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : level k = level i+1
    · rw [maximalStep, ite_eq_left hk, ih k j (by omega)]
    · rw [maximalStep, ite_eq_right hk, zero_mul]
      by_cases hbig : level i+1 < level k
      · rw [hA i k hbig, zero_mul]
      · rw [pow_apply_eq_zero_of_level_gap A level hA n k j (by omega), mul_zero]

/-- One positive path suffices for a strictly positive entry of a nonnegative matrix power. -/
theorem pow_apply_pos_of_positive_path (A : Matrix ι ι ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (n : ℕ) (p : ℕ → ι)
    (hp : ∀ k < n, 0 < A (p k) (p (k+1))) : 0 < (A^n) (p 0) (p n) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply]
    have ht := ih (fun k => p (k+1)) (fun k hk => hp (k+1) (by omega))
    have hv : 0 < A (p 0) (p 1) * (A^n) (p 1) (p (n+1)) :=
      mul_pos (hp 0 (by omega)) ht
    apply hv.trans_le
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (hA (p 0) k) (pow_apply_nonneg hA n k (p (n+1))))
      (Finset.mem_univ (p 1))

/-- Diagonal sign changes telescope along every matrix-power path. -/
theorem pow_apply_sign_conjugate (A : Matrix ι ι ℝ) (s : ι → ℝ)
    (hs : ∀ i, s i*s i=1) (n : ℕ) (i j : ι) :
    ((Matrix.of (fun i j => s i*A i j*s j))^n) i j = s i*(A^n) i j*s j := by
  induction n generalizing i j with
  | zero =>
    by_cases h : i=j
    · subst j; simp [hs]
    · simp [h]
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_apply, mul_apply, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [ih]
    change (s i*A i k*s k)*(s k*(A^n) k j*s j) = s i*(A i k*(A^n) k j)*s j
    calc
      _ = (s i*(A i k*(A^n) k j)*s j)*(s k*s k) := by ring
      _ = _ := by rw [hs, mul_one]

end Matrix
