/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.DifferentialEquation
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Endpoint
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! # Gegenbauer lowering in the orthogonality range

Polynomial identities used in the weighted primitive and the power-law
recurrence. Reference: DLMF 18.9.19 and 18.9.20.
-/

public section
namespace Polynomial

/-- A derivative identity lowering the degree by one. -/
theorem gegenbauer_euler_derivative {lam : ℝ} (hlam : -(1/2) < lam) (n : ℕ) :
    X*derivative (gegenbauer lam (n+1)) - C (n+1 : ℝ)*gegenbauer lam (n+1) =
      derivative (gegenbauer lam n) := by
  cases n with
  | zero => simp [gegenbauer_one]; ring
  | succ n =>
    have hn : (n : ℝ)+lam+2 ≠ 0 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    apply mul_left_cancel₀ (C_ne_zero.mpr hn)
    have hr := gegenbauer_recurrence (lam+1) n
    have hc := gegenbauer_conversion lam n
    rw [derivative_gegenbauer_succ, derivative_gegenbauer_succ]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_ofNat, map_natCast,
      map_one] at hr hc ⊢
    simp only [Nat.add_assoc, Nat.reduceAdd]
    linear_combination -C lam*hr-(n+2 : ℝ[X])*hc

/-- The endpoint normalization satisfies its elementary first-order recurrence. -/
theorem succ_mul_eval_gegenbauer_one (lam : ℝ) (n : ℕ) :
    ((n : ℝ)+1)*(gegenbauer lam (n+1)).eval 1 =
      ((n : ℝ)+2*lam)*(gegenbauer lam n).eval 1 := by
  simp only [eval_gegenbauer_one, ascPochhammer_succ_eval, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul, map_inv₀]
  norm_cast
  push_cast
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

/-- The factor `1-X²` times the derivative has just two adjacent-degree
components (DLMF 18.9.19). -/
theorem gegenbauer_lowering {lam : ℝ} (hlam : -(1/2) < lam) (n : ℕ) :
    (1-X^2)*derivative (gegenbauer lam (n+1)) +
      C (n+1 : ℝ)*X*gegenbauer lam (n+1) =
        C ((n : ℝ)+2*lam)*gegenbauer lam n := by
  let r : ℝ[X] := (1-X^2)*derivative (gegenbauer lam (n+1)) +
    C (n+1 : ℝ)*X*gegenbauer lam (n+1) - C ((n : ℝ)+2*lam)*gegenbauer lam n
  have hd : derivative r = 0 := by
    have ho := gegenbauer_differentialEquation lam (n+1)
    have he := gegenbauer_euler_derivative hlam n
    dsimp only [r]
    simp only [derivative_sub, derivative_add, derivative_mul, derivative_one,
      derivative_X_pow, Nat.cast_ofNat, Nat.reduceSub, pow_one, derivative_C,
      derivative_X, zero_mul, zero_add, zero_sub, mul_one]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_natCast, map_one,
      map_ofNat] at ho he ⊢
    linear_combination ho+((n : ℝ[X])+2*C lam)*he
  have hv : r.eval 1 = 0 := by
    dsimp only [r]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_one,
      one_pow, sub_self, zero_mul, mul_one, zero_add]
    exact sub_eq_zero.mpr (succ_mul_eval_gegenbauer_one lam n)
  have hr := eq_C_of_derivative_eq_zero hd
  have hv' := congrArg (fun q : ℝ[X] ↦ q.eval 1) hr
  rw [hv, eval_C] at hv'
  have hz : r = 0 := by rw [hr, ← hv', C_0]
  exact sub_eq_zero.mp hz

end Polynomial
