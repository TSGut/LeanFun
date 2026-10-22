/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialEquation
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Connection
import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Endpoint bounds for Jacobi polynomials

The differential equation gives a Sonin energy whose derivative changes sign
at most once, from negative to positive, when alpha+beta+1 is nonnegative.
This is an intermediate estimate; parameters with smaller sum are handled by
parameter-raising identities in the subsequent approximation argument.
Reference: DLMF Table 18.8.1, the Jacobi differential equation.
-/

public section
namespace Polynomial
open Set

/-- The derivative of the Jacobi Sonin energy, with no division by the eigenvalue. -/
theorem hasDerivAt_jacobiSoninEnergy (α β : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (n : ℝ) * (n + α + β + 1) * (jacobi α β n).eval t ^ 2 +
      (1 - t ^ 2) * (jacobi α β n).derivative.eval t ^ 2)
      (2 * (α - β + (α + β + 1) * x) * (jacobi α β n).derivative.eval x ^ 2) x := by
  let p := jacobi α β n
  have he := congrArg (fun q : ℝ[X] ↦ q.eval x) (jacobi_differentialEquation α β n)
  simp only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C, eval_zero] at he
  have hd := (((p.hasDerivAt x).pow 2).const_mul ((n : ℝ) * (n + α + β + 1))).add
    (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).mul
      ((p.derivative.hasDerivAt x).pow 2))
  convert hd using 1
  · rfl
  · dsimp [p]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    linear_combination (-2 * ((jacobi α β n).derivative.eval x)) * he

/-- When alpha+beta >= -1, the maximum absolute value on [-1,1] occurs at
an endpoint. This follows directly from the differential equation's energy. -/
theorem abs_eval_jacobi_le_max_endpoints {α β : ℝ} (hs : 0 ≤ α + β + 1)
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(jacobi α β n).eval x| ≤
      max |(jacobi α β n).eval (-1)| |(jacobi α β n).eval 1| := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let c : ℝ := (n : ℝ) * (n + α + β + 1)
  have hc : 0 < c := mul_pos hn0 (by linarith)
  let E := fun t : ℝ ↦ c * (jacobi α β n).eval t ^ 2 +
    (1 - t ^ 2) * (jacobi α β n).derivative.eval t ^ 2
  have hd (t : ℝ) : HasDerivAt E
      (2 * (α - β + (α + β + 1) * t) * (jacobi α β n).derivative.eval t ^ 2) t :=
    hasDerivAt_jacobiSoninEnergy α β n t
  have hcont : Continuous E := continuous_iff_continuousAt.mpr (fun t ↦ (hd t).continuousAt)
  have hlow : c * (jacobi α β n).eval x ^ 2 ≤ E x := by
    dsimp [E]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith) (sq_nonneg _))
  have hupper : E x ≤ max (c * (jacobi α β n).eval (-1) ^ 2)
      (c * (jacobi α β n).eval 1 ^ 2) := by
    by_cases hsign : 0 ≤ α - β + (α + β + 1) * x
    · have hm : MonotoneOn E (Icc x 1) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x 1) hcont.continuousOn
          (fun t _ ↦ (hd t).hasDerivWithinAt)
        intro t ht
        have ht' := interior_subset ht
        have hst : 0 ≤ α - β + (α + β + 1) * t := by
          nlinarith [mul_nonneg hs (sub_nonneg.mpr ht'.1)]
        positivity
      have h := hm (left_mem_Icc.mpr hx.2) (right_mem_Icc.mpr hx.2) hx.2
      apply h.trans
      simp only [E, one_pow, sub_self, zero_mul, add_zero]
      exact le_max_right _ _
    · have hm : AntitoneOn E (Icc (-1) x) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (-1) x) hcont.continuousOn
          (fun t _ ↦ (hd t).hasDerivWithinAt)
        intro t ht
        have ht' := interior_subset ht
        have hst : α - β + (α + β + 1) * t ≤ 0 := by
          nlinarith [mul_nonneg hs (sub_nonneg.mpr ht'.2)]
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hst)
          (sq_nonneg _)
      have h := hm (left_mem_Icc.mpr hx.1) (right_mem_Icc.mpr hx.1) hx.1
      apply h.trans
      norm_num only [E, neg_one_sq, sub_self, zero_mul, add_zero]
      exact le_max_left _ _
  have hsq : (jacobi α β n).eval x ^ 2 ≤
      max ((jacobi α β n).eval (-1) ^ 2) ((jacobi α β n).eval 1 ^ 2) := by
    rw [← mul_max_of_nonneg _ _ hc.le] at hupper
    exact (mul_le_mul_iff_right₀ hc).mp (hlow.trans hupper)
  rcases le_total ((jacobi α β n).eval (-1) ^ 2) ((jacobi α β n).eval 1 ^ 2) with h | h
  · rw [max_eq_right h] at hsq
    apply (show |(jacobi α β n).eval x| ≤ |(jacobi α β n).eval 1| by
      nlinarith [sq_abs ((jacobi α β n).eval x), sq_abs ((jacobi α β n).eval 1),
        abs_nonneg ((jacobi α β n).eval x), abs_nonneg ((jacobi α β n).eval 1)]).trans
    exact le_max_right _ _
  · rw [max_eq_left h] at hsq
    apply (show |(jacobi α β n).eval x| ≤ |(jacobi α β n).eval (-1)| by
      nlinarith [sq_abs ((jacobi α β n).eval x), sq_abs ((jacobi α β n).eval (-1)),
        abs_nonneg ((jacobi α β n).eval x), abs_nonneg ((jacobi α β n).eval (-1))]).trans
    exact le_max_left _ _

/-- Throughout the full orthogonality range, one parameter shift bounds the
polynomial by endpoint values of two members of the shifted family. -/
theorem abs_eval_jacobi_succ_le_shifted_endpoints {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(jacobi α β (n + 1)).eval x| ≤
      max |(jacobi (α + 1) β (n + 1)).eval (-1)| |(jacobi (α + 1) β (n + 1)).eval 1| +
      max |(jacobi (α + 1) β n).eval (-1)| |(jacobi (α + 1) β n).eval 1| := by
  let A := max |(jacobi (α + 1) β (n + 1)).eval (-1)| |(jacobi (α + 1) β (n + 1)).eval 1|
  let B := max |(jacobi (α + 1) β n).eval (-1)| |(jacobi (α + 1) β n).eval 1|
  have hA : 0 ≤ A := (abs_nonneg _).trans (le_max_left _ _)
  have hB : 0 ≤ B := (abs_nonneg _).trans (le_max_left _ _)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : 0 ≤ (α + 1) + β + 1 := by linarith
  have hq := abs_eval_jacobi_le_max_endpoints hs (n + 1) hx
  have hr := abs_eval_jacobi_le_max_endpoints hs n hx
  have he := congrArg (fun p : ℝ[X] ↦ p.eval x) (jacobi_raise_alpha α β n)
  simp only [eval_mul, eval_C, eval_sub] at he
  have hd : 0 < 2 * (n : ℝ) + α + β + 3 := by linarith
  have ha : 0 ≤ (n : ℝ) + α + β + 2 := by linarith
  have hb : 0 ≤ (n : ℝ) + β + 1 := by linarith
  have heabs : (2 * (n : ℝ) + α + β + 3) * |(jacobi α β (n + 1)).eval x| ≤
      ((n : ℝ) + α + β + 2) * A + ((n : ℝ) + β + 1) * B := by
    rw [← abs_of_pos hd, ← abs_mul, he]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    exact add_le_add (mul_le_mul_of_nonneg_left hq ha) (mul_le_mul_of_nonneg_left hr hb)
  have hcmp : ((n : ℝ) + α + β + 2) * A + ((n : ℝ) + β + 1) * B ≤
      (2 * (n : ℝ) + α + β + 3) * (A + B) := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) hA,
      mul_nonneg (show 0 ≤ (n : ℝ) + α + 2 by linarith) hB]
  exact (mul_le_mul_iff_right₀ hd).mp (heabs.trans hcmp)

end Polynomial
