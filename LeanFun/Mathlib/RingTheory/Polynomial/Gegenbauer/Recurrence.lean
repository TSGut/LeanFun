/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Algebra.Algebra.Factorial

public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Conversion

import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Gegenbauer three-term recurrence

The universal polynomial identity has all denominators cleared.
Reference: DLMF Table 18.9.1.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The denominator-cleared Gegenbauer recurrence (DLMF Table 18.9.1). -/
theorem gegenbauer_recurrence (lam : R) (n : ℕ) :
    C (n + 2 : R) * gegenbauer lam (n + 2) -
      C (2 * ((n : R) + lam + 1)) * X * gegenbauer lam (n + 1) +
      C ((n : R) + 2 * lam) * gegenbauer lam n = 0 := by
  let : HasUniqueDiv R := HasUniqueDiv.of_module_rat R
  let r (lam : R) (n : ℕ) := C (n + 2 : R) * gegenbauer lam (n + 2) -
    C (2 * ((n : R) + lam + 1)) * X * gegenbauer lam (n + 1) +
    C ((n : R) + 2 * lam) * gegenbauer lam n
  have hz (lam : R) (n : ℕ) : (r lam n).eval 0 = 0 := by
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · subst n
      have he : 2 * m + 2 = 2 * (m + 1) := by omega
      dsimp only [r]
      rw [he]
      simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, mul_zero, zero_mul,
        sub_zero, eval_gegenbauer_even_zero]
      rw [ascPochhammer_succ_eval]
      have hf : (m + 1 : R) * algebraMap ℚ R (((m + 1).factorial : ℚ)⁻¹) =
          algebraMap ℚ R ((m.factorial : ℚ)⁻¹) :=
        Nat.cast_succ_mul_algebraMap_inv_factorial R m
      rw [← hf]
      simp only [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      ring
    · subst n
      have he : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by omega
      dsimp only [r]
      rw [he]
      simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, mul_zero, zero_mul,
        sub_zero, eval_gegenbauer_odd_zero, add_zero]
  have finish (p : R[X]) (hd : derivative p = 0) (hv : p.eval 0 = 0) : p = 0 := by
    have hc := eq_C_of_derivative_eq_zero hd
    have he := congrArg (fun q : R[X] => q.eval 0) hc
    simp only [eval_C] at he
    have hcoeff := he.symm.trans hv
    rw [hc, hcoeff, C_0]
  have hzero : ∀ n : ℕ, ∀ lam : R, r lam n = 0 := by
    intro n
    induction n with
    | zero =>
      intro lam
      apply finish _ _ (hz lam 0)
      dsimp only [r]
      simp only [Nat.cast_zero, zero_add]
      simp only [derivative_add, derivative_sub, derivative_mul, derivative_C,
        derivative_X, derivative_gegenbauer_succ, gegenbauer_zero, gegenbauer_one,
        zero_mul, zero_add, mul_one, add_zero]
      simp only [map_mul, map_add, map_ofNat, map_one]
      ring
    | succ n ih =>
      intro lam
      apply finish _ _ (hz lam (n + 1))
      have hprev := ih (lam + 1)
      have hconv := gegenbauer_conversion lam n
      dsimp only [r] at hprev ⊢
      simp only [derivative_add, derivative_sub, derivative_mul, derivative_C,
        derivative_X, derivative_gegenbauer_succ, zero_mul, zero_add, mul_one]
      simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_natCast,
        map_ofNat, map_one] at hprev hconv ⊢
      linear_combination (2 * C lam) * hprev - 2 * hconv
  exact hzero n lam

end Polynomial
