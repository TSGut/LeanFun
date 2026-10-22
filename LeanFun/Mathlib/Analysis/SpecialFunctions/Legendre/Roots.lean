/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Legendre.Structure
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Location and interlacing of Legendre roots

All degree-many simple roots lie strictly inside the orthogonality interval.
Reference: DLMF 18.2(vi).
-/
public section
open Set MeasureTheory
namespace Polynomial

private theorem neg_one_lt_root_legendre {n : ℕ} {r : ℝ}
    (hr : (legendre ℝ n).eval r = 0) : -1 < r := by
  by_contra h
  have hrle : r ≤ -1 := le_of_not_gt h
  obtain ⟨q, hpq⟩ := dvd_iff_isRoot.mpr hr
  have hp : legendre ℝ n ≠ 0 := (legendreSequence ℝ).ne_zero n
  have hq : q ≠ 0 := by intro hq; simp [hq] at hpq; exact hp hpq
  have hqd : q.degree < n := by
    rw [← degree_legendre ℝ n, hpq, degree_mul, degree_X_sub_C]
    rw [degree_eq_natDegree hq]
    exact_mod_cast (show q.natDegree < 1 + q.natDegree by omega)
  have hz := integral_mul_legendre_eq_zero_of_degree_lt hqd
  have hex : ∃ x ∈ Ioo (-1 : ℝ) 1, q.eval x ≠ 0 := by
    by_contra he
    push Not at he
    exact hq (q.eq_zero_of_infinite_isRoot
      ((Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).mono he))
  obtain ⟨x, hx, hqx⟩ := hex
  have he (t : ℝ) : q.eval t * (legendre ℝ n).eval t = (t - r) * q.eval t ^ 2 := by
    rw [hpq, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ ↦ 0) (g := fun t ↦ q.eval t * (legendre ℝ n).eval t)
    (show (-1 : ℝ) < 1 by norm_num) continuous_const.continuousOn
    (q.continuous.mul (legendre ℝ n).continuous).continuousOn
    (fun t ht ↦ by rw [he]; exact mul_nonneg (by linarith [ht.1]) (sq_nonneg _))
    ⟨x, Ioo_subset_Icc_self hx, by rw [he]; exact mul_pos (by linarith [hx.1]) (sq_pos_of_ne_zero hqx)⟩
  rw [intervalIntegral.integral_zero, hz] at hi
  exact lt_irrefl _ hi

/-- Every Legendre root lies in the open interval `(-1,1)` (DLMF 18.2(vi)). -/
theorem root_legendre_mem_Ioo {n : ℕ} {x : ℝ} (hx : (legendre ℝ n).eval x = 0) :
    x ∈ Ioo (-1) 1 := by
  have hleft := neg_one_lt_root_legendre hx
  have hneg : (legendre ℝ n).eval (-x) = 0 := by rw [eval_legendre_neg, hx, mul_zero]
  have hright := neg_one_lt_root_legendre hneg
  exact ⟨hleft, by linarith⟩

/-- Consecutive Legendre polynomials have no common root (DLMF 18.2(vi)). -/
theorem not_eval_legendre_eq_zero_and_succ (n : ℕ) (x : ℝ) :
    ¬ ((legendre ℝ n).eval x = 0 ∧ (legendre ℝ (n + 1)).eval x = 0) :=
  isOrthogonal_legendreSequence.not_eval_eq_zero_and_succ hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure n x

/-- Between distinct degree-`n` Legendre roots is a degree-`n+1` root (DLMF 18.2(vi)). -/
theorem exists_root_legendre_succ_between (n : ℕ) {a b : ℝ} (hab : a < b)
    (ha : (legendre ℝ n).eval a = 0) (hb : (legendre ℝ n).eval b = 0) :
    ∃ c ∈ Ioo a b, (legendre ℝ (n + 1)).eval c = 0 :=
  isOrthogonal_legendreSequence.exists_root_succ_between hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure n hab ha hb

/-- Between distinct degree-`n+1` Legendre roots is a degree-`n` root (DLMF 18.2(vi)). -/
theorem exists_root_legendre_between_succ (n : ℕ) {a b : ℝ} (hab : a < b)
    (ha : (legendre ℝ (n + 1)).eval a = 0) (hb : (legendre ℝ (n + 1)).eval b = 0) :
    ∃ c ∈ Ioo a b, (legendre ℝ n).eval c = 0 :=
  isOrthogonal_legendreSequence.exists_root_between_succ hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure n hab ha hb

/-- The higher-degree Legendre member has both outermost roots (DLMF 18.2(vi)). -/
theorem exists_outer_roots_legendre {n : ℕ} (hn : 1 ≤ n) :
    ∃ a b : ℝ, a < b ∧ (legendre ℝ (n + 1)).eval a = 0 ∧
      (legendre ℝ (n + 1)).eval b = 0 ∧
      ∀ x : ℝ, (legendre ℝ n).eval x = 0 → a < x ∧ x < b :=
  isOrthogonal_legendreSequence.exists_outer_roots hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure hn

end Polynomial
