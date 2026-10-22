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
# Gegenbauer parameter conversion

All parameter denominators are cleared. Reference: DLMF 18.9.7.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The constant initial case of parameter conversion (DLMF 18.9.7). -/
theorem gegenbauer_conversion_zero (lam : R) :
    C lam * gegenbauer lam 0 = C lam * gegenbauer (lam + 1) 0 := by simp

/-- The linear initial case of parameter conversion (DLMF 18.9.7). -/
theorem gegenbauer_conversion_one (lam : R) :
    C (lam + 1) * gegenbauer lam 1 = C lam * gegenbauer (lam + 1) 1 := by
  simp only [gegenbauer_one, map_mul]
  ring

/-- The denominator-cleared parameter conversion identity (DLMF 18.9.7). -/
theorem gegenbauer_conversion (lam : R) (n : ℕ) :
    C ((n : R) + lam + 2) * gegenbauer lam (n + 2) =
      C lam * (gegenbauer (lam + 1) (n + 2) - gegenbauer (lam + 1) n) := by
  let : HasUniqueDiv R := HasUniqueDiv.of_module_rat R
  let r (lam : R) (n : ℕ) := C ((n : R) + lam + 2) * gegenbauer lam (n + 2) -
    C lam * (gegenbauer (lam + 1) (n + 2) - gegenbauer (lam + 1) n)
  have hz (lam : R) (n : ℕ) : (r lam n).eval 0 = 0 := by
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · subst n
      have he : 2 * m + 2 = 2 * (m + 1) := by omega
      dsimp only [r]
      rw [he]
      simp only [eval_sub, eval_mul, eval_C, eval_gegenbauer_even_zero]
      have hl : (ascPochhammer R (m + 1)).eval lam =
          lam * (ascPochhammer R m).eval (lam + 1) := by
        rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp,
          eval_add, eval_X, eval_one]
      rw [hl, ascPochhammer_succ_eval]
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
      simp only [eval_sub, eval_mul, eval_C, eval_gegenbauer_odd_zero,
        mul_zero, sub_self]
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
      simp only [derivative_sub, derivative_C_mul, derivative_gegenbauer_succ,
        gegenbauer_zero, gegenbauer_one, derivative_one, sub_zero]
      simp only [map_mul, map_add, map_ofNat, map_one]
      ring
    | succ n ih =>
      intro lam
      apply finish _ _ (hz lam (n + 1))
      have hprev := ih (lam + 1)
      dsimp only [r] at hprev ⊢
      simp only [derivative_sub, derivative_C_mul, derivative_gegenbauer_succ]
      simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_natCast,
        map_ofNat, map_one] at hprev ⊢
      linear_combination (2 * C lam) * hprev
  exact sub_eq_zero.mp (hzero n lam)

end Polynomial
