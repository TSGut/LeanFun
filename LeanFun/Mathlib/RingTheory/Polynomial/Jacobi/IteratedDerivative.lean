/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Derivative

/-! # Jacobi derivatives of arbitrary order
The finite product is the rising-factorial coefficient in the iteration of
DLMF 18.9.15. This holds over every commutative rational algebra.
-/

public section
namespace Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Iterating the Jacobi derivative shifts both parameters by the derivative
order. The index n+k includes every surviving mode. -/
theorem iterate_derivative_jacobi (α β : R) (k n : ℕ) :
    derivative^[k] (jacobi α β (n + k)) =
      C (∏ j ∈ Finset.range k, algebraMap ℚ R (1 / 2) *
        ((n + k : R) + α + β + j + 1)) * jacobi (α + k) (β + k) n := by
  induction k generalizing α β with
  | zero => simp
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 by omega,
      Function.iterate_succ_apply, derivative_jacobi_succ, iterate_derivative_C_mul, ih]
    simp only [Finset.prod_range_succ', Nat.cast_add, Nat.cast_one]
    rw [← mul_assoc, ← map_mul]
    congr 1
    · congr 1
      rw [mul_comm]
      congr 1
      · apply Finset.prod_congr rfl
        intro j _
        ring
      · simp only [Nat.cast_zero]; ring
    · congr 1 <;> ring

/-- Modes below the derivative order vanish, including degenerate parameters. -/
theorem iterate_derivative_jacobi_eq_zero (α β : R) {k n : ℕ} (hn : n < k) :
    derivative^[k] (jacobi α β n) = 0 := by
  exact iterate_derivative_eq_zero ((natDegree_jacobi_le α β n).trans_lt hn)

end Polynomial
