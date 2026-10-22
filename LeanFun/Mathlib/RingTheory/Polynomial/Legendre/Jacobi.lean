/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Legendre
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialEquation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Legendre–Jacobi bridge

The independently defined Rodrigues family is the Jacobi family at parameters
zero. References: DLMF Table 18.3.1 and 18.5.7.
-/

public section

namespace Polynomial

variable (R : Type*) [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
private theorem pochhammer_nat_succ (n k : ℕ) :
    (ascPochhammer R k).eval ((n : R) + 1) =
      (k.factorial : R) * ((n + k).choose k : R) := by
  rw [show (n : R) + 1 = ((n + 1 : ℕ) : R) by push_cast; rfl,
    ← Nat.cast_ascFactorial, Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul]

/-- The Rodrigues Legendre family equals the Jacobi family with both parameters
zero (DLMF Table 18.3.1). -/
theorem legendre_eq_jacobi (n : ℕ) : legendre R n = jacobi (0 : R) 0 n := by
  rw [legendre_eq_shiftedLegendre_comp]
  simp only [shiftedLegendre, jacobi, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_natCast,
    neg_comp, one_comp, natCast_comp, map_X, sum_comp, mul_comp, pow_comp, X_comp,
    map_mul, map_pow, map_neg, map_one, map_natCast, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using hk
  have hchoose : (n + k).choose k = (n + k).choose n := by
    simpa using (Nat.choose_symm (Nat.le_add_left k n)).symm
  rw [pochhammer_nat_succ, pochhammer_nat_succ, Nat.add_sub_of_le hkn,
    Nat.choose_symm hkn, hchoose]
  have hc : algebraMap ℚ R (((k.factorial : ℚ) * (n - k).factorial * 2 ^ k)⁻¹) *
      (k.factorial : R) * ((n - k).factorial : R) = algebraMap ℚ R ((1 / 2 : ℚ) ^ k) := by
    have h : (((k.factorial : ℚ) * (n - k).factorial * 2 ^ k)⁻¹) *
        k.factorial * (n - k).factorial = (1 / 2 : ℚ) ^ k := by
      rw [div_pow, one_pow]
      field_simp
    simpa only [map_mul, map_natCast] using congrArg (algebraMap ℚ R) h
  have hbase : (C (-1 : R) * (C (algebraMap ℚ R (1 / 2)) * (1 - X))) =
      C (algebraMap ℚ R (1 / 2)) * (X - 1) := by simp only [map_neg, map_one]; ring
  calc
    _ = C (n.choose k : R) * C ((n + k).choose n : R) *
        (C (-1 : R) * (C (algebraMap ℚ R (1 / 2)) * (1 - X))) ^ k := by
      simp only [mul_pow, map_neg, map_one, map_natCast]
      ring
    _ = C (n.choose k : R) * C ((n + k).choose n : R) *
        (C (algebraMap ℚ R (1 / 2)) * (X - 1)) ^ k := by rw [hbase]
    _ = C (algebraMap ℚ R (((k.factorial : ℚ) * (n - k).factorial * 2 ^ k)⁻¹) *
        (k.factorial : R) * ((n - k).factorial : R)) *
        C (n.choose k : R) * C ((n + k).choose n : R) * (X - 1) ^ k := by
      rw [hc]
      simp only [map_pow, mul_pow]
      ring
    _ = _ := by simp only [map_mul]; ring

end Polynomial
