/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.NumberTheory.Harmonic.Bounds

import Mathlib.Tactic.Linarith

/-!
# A harmonic bound for a finite family with reciprocal-distance decay

Separate the two indices surrounding a real number and sum reciprocal distances
on each side. This is used in the Chebyshev Lebesgue estimate (ATAP, Chapter 15).
-/

public section

/-- The harmonic logarithmic bound at a positive natural index (ATAP, Chapter 15).
The index type excludes evaluation of the logarithm at zero. -/
theorem harmonic_le_one_add_log_of_pos (n : {n : ℕ // 0 < n}) :
    (harmonic n.val : ℝ) ≤ 1 + Real.log n.val :=
  harmonic_le_one_add_log n.val

namespace Finset

/-- A bounded nonnegative family with inverse-distance decay has a harmonic sum bound
(ATAP, Chapter 15, elementary estimate). -/
theorem sum_le_two_mul_add_harmonic {N : ℕ} {t M : ℝ} {a : ℕ → ℝ}
    (ht0 : 0 ≤ t) (htN : t ≤ N) (hM : 0 ≤ M)
    (ha0 : ∀ j ≤ N, 0 ≤ a j) (haM : ∀ j ≤ N, a j ≤ M)
    (ha : ∀ j ≤ N, |t - j| * a j ≤ 1) :
    ∑ j ∈ range (N + 1), a j ≤ 2 * M + 2 * (harmonic N : ℝ) := by
  let k := ⌊t⌋₊
  have hk : k ≤ N := Nat.floor_le_of_le htN
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht0
  have htk : t < k + 1 := Nat.lt_floor_add_one t
  have hsum {m : ℕ} (hm : m ≤ N) :
      ∑ j ∈ range m, ((j : ℝ) + 1)⁻¹ ≤ (harmonic N : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one, Nat.cast_add, Nat.cast_one]
    apply sum_le_sum_of_subset_of_nonneg (range_mono hm)
    intro i _ _
    positivity
  have hrec {j r : ℕ} (hr : r ≤ N) (hd : (j : ℝ) + 1 ≤ |t - r|) :
      a r ≤ ((j : ℝ) + 1)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < j + 1)).mpr
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right hd (ha0 r hr)).trans (ha r hr)
  have hl : ∑ j ∈ range (k + 1), a j ≤ M + (harmonic N : ℝ) := by
    rw [sum_range_succ, ← sum_range_reflect a k]
    have hb : ∑ j ∈ range k, a (k - 1 - j) ≤
        ∑ j ∈ range k, ((j : ℝ) + 1)⁻¹ := by
      apply sum_le_sum
      intro j hj
      have hjk : j < k := mem_range.mp hj
      apply hrec (by omega)
      have hc : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
      rw [abs_of_nonneg (by
        rw [hc]
        linarith only [hkt, htk, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]), hc]
      linarith
    linarith [hb.trans (hsum hk), haM k hk]
  have hr : ∑ j ∈ range (N - k), a (k + 1 + j) ≤ M + (harmonic N : ℝ) := by
    cases hm : N - k with
    | zero =>
      simp only [sum_range_zero]
      exact add_nonneg hM ((show (0 : ℝ) ≤ ∑ j ∈ range 0, ((j : ℝ) + 1)⁻¹ by simp).trans
        (hsum (Nat.zero_le N)))
    | succ m =>
      rw [sum_range_succ']
      have hb : ∑ j ∈ range m, a (k + 1 + (j + 1)) ≤
          ∑ j ∈ range m, ((j : ℝ) + 1)⁻¹ := by
        apply sum_le_sum
        intro j hj
        have hjm : j < m := mem_range.mp hj
        apply hrec (by omega)
        have hc : ((k + 1 + (j + 1) : ℕ) : ℝ) = (k : ℝ) + j + 2 := by
          push_cast
          ring
        rw [abs_of_nonpos (by
          rw [hc]
          linarith only [hkt, htk, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]), hc]
        linarith
      have hb' := hb.trans (hsum (show m ≤ N by omega))
      have hfirst := haM (k + 1) (by omega)
      simpa only [Nat.add_zero] using add_le_add hb' hfirst |>.trans_eq (add_comm _ _)
  have he : N + 1 = (k + 1) + (N - k) := by omega
  rw [he, sum_range_add]
  linarith

end Finset
