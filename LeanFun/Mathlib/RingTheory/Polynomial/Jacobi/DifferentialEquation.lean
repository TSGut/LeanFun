/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Algebra.Algebra.Factorial

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Derivative

import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Jacobi differential equation

The polynomial equation includes every specialisation of the parameters in a
commutative rational algebra. Reference: DLMF Table 18.8.1.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The Jacobi differential equation, without parameter restrictions
(DLMF Table 18.8.1). -/
theorem jacobi_differentialEquation (α β : R) (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (jacobi α β n)) +
      (C (β - α) - C (α + β + 2) * X) * derivative (jacobi α β n) +
      C ((n : R) * ((n : R) + α + β + 1)) * jacobi α β n = 0 := by
  let : HasUniqueDiv R := HasUniqueDiv.of_module_rat R
  induction n generalizing α β with
  | zero => simp
  | succ n ih =>
    let p := jacobi α β (n + 1)
    let q := jacobi (α + 1) (β + 1) n
    let d := algebraMap ℚ R (1 / 2) * ((n : R) + α + β + 2)
    let r := (1 - X ^ 2) * derivative (derivative p) +
      (C (β - α) - C (α + β + 2) * X) * derivative p +
      C (((n + 1 : ℕ) : R) * (((n + 1 : ℕ) : R) + α + β + 1)) * p
    have hp : derivative p = C d * q := derivative_jacobi_succ α β n
    have hr : derivative r = 0 := by
      dsimp only [r]
      simp only [derivative_add, derivative_mul, derivative_sub, derivative_one,
        derivative_X_pow, derivative_X, derivative_C, zero_mul, zero_sub,
        zero_add, mul_one]
      rw [hp, derivative_C_mul, derivative_C_mul]
      have hi := ih (α + 1) (β + 1)
      change (1 - X ^ 2) * derivative (derivative q) +
        (C ((β + 1) - (α + 1)) - C ((α + 1) + (β + 1) + 2) * X) * derivative q +
        C ((n : R) * ((n : R) + (α + 1) + (β + 1) + 1)) * q = 0 at hi
      simp only [Nat.cast_add, Nat.cast_one, map_add, map_sub, map_mul,
        map_natCast, map_ofNat, map_one] at hi ⊢
      linear_combination C d * hi
    have hhalf : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
      have h := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
      simpa only [map_mul, map_ofNat, map_one] using h
    have hfact : (n + 1 : R) * algebraMap ℚ R (((n + 1).factorial : ℚ)⁻¹) =
        algebraMap ℚ R ((n.factorial : ℚ)⁻¹) :=
      Nat.cast_succ_mul_algebraMap_inv_factorial R n
    have heval : r.eval 1 = 0 := by
      dsimp only [r]
      simp only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X,
        one_pow, sub_self, zero_mul, zero_add, eval_C, mul_one]
      rw [hp, eval_mul, eval_C]
      dsimp only [p, q, d]
      rw [eval_jacobi_one, eval_jacobi_one, ascPochhammer_succ_left,
        eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one]
      simp only [Nat.cast_add, Nat.cast_one]
      have harg : (n : R) + 1 + α + β + 1 = n + α + β + 2 := by ring
      rw [harg]
      calc
        _ = (-(2 * algebraMap ℚ R (1 / 2)) * algebraMap ℚ R ((n.factorial : ℚ)⁻¹) +
            (n + 1 : R) * algebraMap ℚ R (((n + 1).factorial : ℚ)⁻¹)) *
            ((n : R) + α + β + 2) * (α + 1) *
            (ascPochhammer R n).eval (α + 1 + 1) := by ring
        _ = 0 := by rw [hhalf, hfact]; ring
    have hconst := eq_C_of_derivative_eq_zero hr
    have hc := congrArg (fun p : R[X] => p.eval 1) hconst
    simp only [eval_C] at hc
    have hcoeff : r.coeff 0 = 0 := hc.symm.trans heval
    change r = 0
    rw [hconst, hcoeff, C_0]

end Polynomial
