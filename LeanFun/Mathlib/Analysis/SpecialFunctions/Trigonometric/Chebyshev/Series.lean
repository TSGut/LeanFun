/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Chebyshev series and coefficient tails

The tail estimate common to algebraic and geometric approximation bounds.
Reference: ATAP, Chapters 4, 7 and 8.
-/

public section

namespace Polynomial.Chebyshev

/-- The absolute-tail estimate also holds for vector-valued coefficients, in
particular for complex coefficients (ATAP, equation 4.8). -/
theorem norm_sub_sum_smul_le_tsum_tail {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a : ℕ → E} {f : ℝ → E}
    (ha : Summable (fun n ↦ ‖a n‖)) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1)
    (hf : HasSum (fun n : ℕ ↦ (T ℝ n).eval x • a n) (f x)) (N : ℕ) :
    ‖f x - ∑ n ∈ Finset.range (N + 1), (T ℝ n).eval x • a n‖ ≤
      ∑' k, ‖a (k + (N + 1))‖ := by
  have hb (n : ℕ) : ‖(T ℝ n).eval x • a n‖ ≤ ‖a n‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_eval_T_real_le_one _ (abs_le.mpr hx))
  have hs := ha.of_norm_bounded hb
  have ht := (summable_nat_add_iff (N + 1)).2 ha
  have hn : Summable (fun k ↦ ‖(T ℝ (k + (N + 1) : ℕ)).eval x • a (k + (N + 1))‖) :=
    ht.of_norm_bounded (fun k ↦ by simpa only [norm_norm] using hb (k + (N + 1)))
  have he := hs.sum_add_tsum_nat_add (N + 1)
  rw [hf.tsum_eq] at he
  rw [← he, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun k ↦ hb _) ht)

/-- Absolute summability of coefficients implies convergence at every point of the
approximation interval (ATAP, Chapter 4). -/
theorem summable_mul_eval_T {a : ℕ → ℝ} (ha : Summable (fun n ↦ |a n|))
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    Summable (fun n ↦ a n * (T ℝ n).eval x) := by
  apply ha.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_eval_T_real_le_one _ (abs_le.mpr hx))

/-- A convergent Chebyshev expansion has truncation error bounded by its absolute
coefficient tail (ATAP, equation 4.8). Representation of the function is an explicit
hypothesis; coefficient decay alone is not used to assume it. -/
theorem abs_sub_sum_le_tsum_tail {a : ℕ → ℝ} {f : ℝ → ℝ}
    (ha : Summable (fun n ↦ |a n|)) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1)
    (hf : HasSum (fun n ↦ a n * (T ℝ n).eval x) (f x)) (N : ℕ) :
    |f x - ∑ n ∈ Finset.range (N + 1), a n * (T ℝ n).eval x| ≤
      ∑' k, |a (k + (N + 1))| := by
  have hs := summable_mul_eval_T ha hx
  have ht := (summable_nat_add_iff (N + 1)).2 ha
  have hb (k : ℕ) : ‖a (k + (N + 1)) * (T ℝ (k + (N + 1))).eval x‖ ≤
      |a (k + (N + 1))| := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_eval_T_real_le_one _ (abs_le.mpr hx))
  have he := hs.sum_add_tsum_nat_add (N + 1)
  rw [hf.tsum_eq] at he
  rw [← he, add_sub_cancel_left, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm (ht.of_norm_bounded (fun k ↦ by
    simpa only [norm_norm, Nat.cast_add, Nat.cast_one] using hb k))).trans
    ((ht.of_norm_bounded (fun k ↦ by simpa only [norm_norm, Nat.cast_add, Nat.cast_one] using hb k)).tsum_le_tsum hb ht)

/-- A geometric coefficient bound gives a geometric truncation bound, once the
series represents the function (ATAP, Theorem 8.2, summation step). -/
theorem abs_sub_sum_le_geometric {a : ℕ → ℝ} {f : ℝ → ℝ} {C q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ n, |a n| ≤ C * q ^ n) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1)
    (hf : HasSum (fun n ↦ a n * (T ℝ n).eval x) (f x)) (N : ℕ) :
    |f x - ∑ n ∈ Finset.range (N + 1), a n * (T ℝ n).eval x| ≤
      C * q ^ (N + 1) / (1 - q) := by
  have hg := (summable_geometric_of_lt_one hq hq1).mul_left C
  have hs : Summable (fun n ↦ |a n|) := hg.of_norm_bounded (fun n ↦ by
    simpa only [Real.norm_eq_abs, abs_abs] using ha n)
  apply (abs_sub_sum_le_tsum_tail hs hx hf N).trans
  have ht := (summable_nat_add_iff (N + 1)).2 hs
  have hg' := (summable_nat_add_iff (N + 1)).2 hg
  calc
    _ ≤ ∑' k, C * q ^ (k + (N + 1)) := ht.tsum_le_tsum (fun k ↦ ha _) hg'
    _ = C * q ^ (N + 1) / (1 - q) := by
      have he (k : ℕ) : C * q ^ (k + (N + 1)) = (C * q ^ (N + 1)) * q ^ k := by
        rw [pow_add]
        ring
      simp_rw [he]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1]
      ring

end Polynomial.Chebyshev
