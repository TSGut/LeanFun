/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Chebyshev.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FieldSimp

/-! # Definite integration of Chebyshev expansions
Exact coefficient integration is the foundation of Clenshaw–Curtis quadrature.
Reference: ATAP, Chapter 19.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open MeasureTheory

/-- Integrating a mode is exactly the endpoint difference of its sparse primitive. -/
theorem integral_eval_T_eq_primitive (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (T ℝ n).eval x =
      (primitiveT ℝ n).eval 1 - (primitiveT ℝ n).eval (-1) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ (primitiveT ℝ n).hasDerivAt x)
    ((primitiveT ℝ n).derivative.continuous.intervalIntegrable (-1) 1)
  simpa only [derivative_primitiveT] using h


/-- The exact unweighted Chebyshev moment; the odd mode of index one is explicit.
Reference: ATAP, Chapter 19. -/
noncomputable def integralMoment (n : ℕ) : ℝ :=
  if n = 1 then 0 else (1 + (-1 : ℝ) ^ n) / (1 - (n : ℝ) ^ 2)


/-- The nonexceptional moment formula has a nonzero denominator. -/
theorem integralMoment_denominator_ne_zero (n : {n : ℕ // n ≠ 1}) :
    1 - (n.val : ℝ) ^ 2 ≠ 0 := by
  have h := Nat.cast_nonneg (α := ℝ) n.val
  have hn : (n.val : ℝ) ≠ 1 := by exact_mod_cast n.property
  intro he
  have : (n.val : ℝ) = 1 := by nlinarith
  exact hn this

/-- The unweighted moment is the actual integral of its polynomial mode. -/
theorem integral_eval_T (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (T ℝ n).eval x = integralMoment n := by
  rw [integral_eval_T_eq_primitive]
  rcases n with _ | _ | n
  · norm_num [primitiveT, integralMoment]
  · norm_num [primitiveT, integralMoment, eval_mul, T_eval_one, T_eval_neg_one]
  · rw [integralMoment, ite_eq_right (by omega)]
    have ht (m : ℕ) : (T ℝ m).eval (-1) = (-1 : ℝ) ^ m := by
      rw [T_eval_neg_one, Int.cast_negOnePow_natCast]
    simp only [primitiveT, eval_sub, eval_mul, eval_C, T_eval_one, ht, mul_one]
    simp only [Nat.cast_add, Nat.cast_one]
    have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
    have h₃ : (n : ℝ) + 3 ≠ 0 := by positivity
    have hden : 1 - ((n : ℝ) + 1 + 1) ^ 2 ≠ 0 := by
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    simp only [pow_succ]
    field_simp
    ring

/-- The usual parity form of the unweighted Chebyshev moments (ATAP, Chapter 19). -/
theorem integral_eval_T_eq_ite (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (T ℝ n).eval x =
      if Even n then 2 / (1 - (n : ℝ) ^ 2) else 0 := by
  rw [integral_eval_T]
  by_cases h1 : n = 1
  · subst n
    norm_num [integralMoment]
  rw [integralMoment, ite_eq_right h1]
  by_cases h : Even n
  · rw [h.neg_one_pow, ite_eq_left h]
    norm_num
  · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow, ite_eq_right h]
    simp

/-- Classical parity characterization of unweighted moments. -/
theorem integralMoment_eq_ite (n : ℕ) :
    integralMoment n = if Even n then 2 / (1 - (n : ℝ) ^ 2) else 0 := by
  rw [← integral_eval_T, integral_eval_T_eq_ite]

/-- Integration of a finite Chebyshev expansion is a weighted coefficient sum. -/
theorem integral_sum_eval_T (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x in (-1 : ℝ)..1, ∑ n ∈ s, a n * (T ℝ n).eval x) =
      ∑ n ∈ s, a n * integralMoment n := by
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, integral_eval_T]
  · intro n _
    exact (continuous_const.mul (T ℝ n).continuous).intervalIntegrable _ _

end Polynomial.Chebyshev
