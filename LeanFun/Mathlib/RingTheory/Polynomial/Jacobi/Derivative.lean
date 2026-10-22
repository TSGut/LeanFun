/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi
public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Derivatives of Jacobi polynomials

The derivative formula holds over any commutative rational algebra, without
restrictions on the parameters. Reference: DLMF 18.9.15.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Differentiation raises both Jacobi parameters by one (DLMF 18.9.15). -/
theorem derivative_jacobi_succ (α β : R) (n : ℕ) :
    derivative (jacobi α β (n + 1)) =
      C (algebraMap ℚ R (1 / 2) * ((n : R) + α + β + 2)) *
        jacobi (α + 1) (β + 1) n := by
  let c (α β : R) (n l : ℕ) : R :=
    algebraMap ℚ R (((l.factorial : ℚ) * (n - l).factorial * 2 ^ l)⁻¹) *
      (ascPochhammer R l).eval ((n : R) + α + β + 1) *
      (ascPochhammer R (n - l)).eval (α + l + 1)
  have hrat (l : ℕ) :
      (l + 1 : ℚ) * (((l + 1).factorial : ℚ) * (n - l).factorial * 2 ^ (l + 1))⁻¹ =
      (1 / 2 : ℚ) * (((l.factorial : ℚ) * (n - l).factorial * 2 ^ l)⁻¹) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hc (l : ℕ) : c α β (n + 1) (l + 1) * (l + 1 : R) =
      (algebraMap ℚ R (1 / 2) * ((n : R) + α + β + 2)) *
        c (α + 1) (β + 1) n l := by
    have hm := congrArg (algebraMap ℚ R) (hrat l)
    simp only [map_mul, map_add, map_natCast, map_one] at hm
    dsimp only [c]
    rw [Nat.add_sub_add_right, ascPochhammer_succ_left, eval_mul, eval_X,
      eval_comp, eval_add, eval_X, eval_one]
    simp only [Nat.cast_add, Nat.cast_one]
    have h1 : (n : R) + 1 + α + β + 1 = n + α + β + 2 := by ring
    have h2 : (n : R) + α + β + 2 + 1 = n + (α + 1) + (β + 1) + 1 := by ring
    have h3 : α + ((l : R) + 1) + 1 = (α + 1) + l + 1 := by ring
    rw [h1, h2, h3]
    calc
      _ = ((l + 1 : R) * algebraMap ℚ R
          ((( (l + 1).factorial : ℚ) * (n - l).factorial * 2 ^ (l + 1))⁻¹)) *
          ((n : R) + α + β + 2) *
          (ascPochhammer R l).eval ((n : R) + (α + 1) + (β + 1) + 1) *
          (ascPochhammer R (n - l)).eval ((α + 1) + l + 1) := by ring
      _ = _ := by rw [hm]; ring
  change derivative (∑ l ∈ Finset.range (n + 1 + 1), C (c α β (n + 1) l) *
    (X - 1) ^ l) = C _ * ∑ l ∈ Finset.range (n + 1),
      C (c (α + 1) (β + 1) n l) * (X - 1) ^ l
  rw [derivative_sum, Finset.sum_range_succ']
  simp only [pow_zero, mul_one, derivative_C, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [derivative_C_mul, derivative_pow_succ, derivative_sub, derivative_X,
    derivative_one, sub_zero, mul_one, ← mul_assoc, ← C_mul, hc, C_mul, mul_assoc]

end Polynomial
