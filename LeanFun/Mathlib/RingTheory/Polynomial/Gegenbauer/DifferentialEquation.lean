/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Algebra.Algebra.Factorial

public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Derivative
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Values

import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Gegenbauer differential equation

All parameters in a commutative rational algebra are allowed.
Reference: DLMF Table 18.8.1.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The Gegenbauer differential equation (DLMF Table 18.8.1). -/
theorem gegenbauer_differentialEquation (lam : R) (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (gegenbauer lam n)) -
      C (2 * lam + 1) * X * derivative (gegenbauer lam n) +
      C ((n : R) * ((n : R) + 2 * lam)) * gegenbauer lam n = 0 := by
  let : HasUniqueDiv R := HasUniqueDiv.of_module_rat R
  let r (lam : R) (n : ℕ) :=
    (1 - X ^ 2) * derivative (derivative (gegenbauer lam n)) -
      C (2 * lam + 1) * X * derivative (gegenbauer lam n) +
      C ((n : R) * ((n : R) + 2 * lam)) * gegenbauer lam n
  have hz (lam : R) (n : ℕ) : (r lam n).eval 0 = 0 := by
    rcases n with _ | (_ | n)
    · simp [r]
    · simp [r, gegenbauer_one]
    · dsimp only [r]
      simp only [derivative_gegenbauer_succ, derivative_C_mul, eval_add, eval_sub,
        eval_mul, eval_C, eval_one, eval_pow, eval_X, zero_pow (by decide : 2 ≠ 0),
        sub_zero, one_mul, mul_zero, zero_mul]
      obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
      · subst n
        have he : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
        rw [he]
        simp only [eval_gegenbauer_even_zero]
        have hl : (ascPochhammer R (m + 1)).eval lam =
            lam * (ascPochhammer R m).eval (lam + 1) := by
          rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp,
            eval_add, eval_X, eval_one]
        have hpo : (lam + 1) * (ascPochhammer R m).eval (lam + 1 + 1) =
            (ascPochhammer R m).eval (lam + 1) * (lam + 1 + m) := by
          rw [← ascPochhammer_succ_eval]
          rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp,
            eval_add, eval_X, eval_one]
        rw [hl]
        have hf : (m + 1 : R) * algebraMap ℚ R (((m + 1).factorial : ℚ)⁻¹) =
            algebraMap ℚ R ((m.factorial : ℚ)⁻¹) :=
          Nat.cast_succ_mul_algebraMap_inv_factorial R m
        rw [← hf]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
        linear_combination (4 * lam * (-1 : R) ^ m * ((m + 1 : R) *
          algebraMap ℚ R (((m + 1).factorial : ℚ)⁻¹))) * hpo
      · subst n
        have he : 2 * m + 1 + 1 + 1 = 2 * (m + 1) + 1 := by omega
        rw [he]
        simp only [eval_gegenbauer_odd_zero, mul_zero, add_zero]
  have hzero : ∀ n : ℕ, ∀ lam : R, r lam n = 0 := by
    intro n
    induction n with
    | zero => intro lam; simp [r]
    | succ n ih =>
      intro lam
      have hd : derivative (r lam (n + 1)) = 0 := by
        have hi := ih (lam + 1)
        dsimp only [r] at hi ⊢
        simp only [derivative_add, derivative_sub, derivative_mul, derivative_one,
          derivative_X_pow, derivative_X, derivative_C, zero_mul, zero_add,
          zero_sub, mul_one]
        rw [derivative_gegenbauer_succ, derivative_C_mul, derivative_C_mul]
        simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_natCast,
          map_ofNat, map_one] at hi ⊢
        linear_combination (2 * C lam) * hi
      have hc := eq_C_of_derivative_eq_zero hd
      have he := congrArg (fun p : R[X] => p.eval 0) hc
      simp only [eval_C] at he
      have hcoeff := he.symm.trans (hz lam (n + 1))
      rw [hc, hcoeff, C_0]
  exact hzero n lam

end Polynomial
