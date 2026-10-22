/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Shifted
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Recurrence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Shifted Jacobi multiplication in the Volterra basis

Explicit multiplication coefficients for the raw shifted (1,0) Jacobi basis.
Reference: DLMF 18.9.2 and Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
namespace Polynomial

/-- The upper multiplication coefficient in the raw shifted (1,0) basis. -/
def shiftedJacobiOneZeroUpper (n : ℕ) : ℝ := ((n : ℝ)+2)/(2*(2*n+3))

/-- The diagonal multiplication coefficient in the raw shifted (1,0) basis. -/
def shiftedJacobiOneZeroDiag (n : ℕ) : ℝ := 1/2-1/(2*(2*n+1)*(2*n+3))

/-- The lower multiplication coefficient in the raw shifted (1,0) basis. -/
def shiftedJacobiOneZeroLower (n : ℕ) : ℝ := (n : ℝ)/(2*(2*n+1))

/-- Multiplication by x in every positive-degree raw shifted Jacobi column. -/
theorem X_mul_shiftedJacobi_one_zero_succ (n : ℕ) :
    X*shiftedJacobi 1 0 (n+1) =
      C (shiftedJacobiOneZeroUpper (n+1))*shiftedJacobi 1 0 (n+2) +
      C (shiftedJacobiOneZeroDiag (n+1))*shiftedJacobi 1 0 (n+1) +
      C (shiftedJacobiOneZeroLower (n+1))*shiftedJacobi 1 0 n := by
  apply Polynomial.funext
  intro x
  have h := congrArg (fun p : ℝ[X] ↦ p.eval (2*x-1)) (jacobi_recurrence (1 : ℝ) 0 n)
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_X] at h
  simp only [eval_mul, eval_add, eval_C, eval_X, eval_shiftedJacobi,
    shiftedJacobiOneZeroUpper, shiftedJacobiOneZeroDiag, shiftedJacobiOneZeroLower,
    Nat.cast_add, Nat.cast_one]
  have h3 : (2*(n : ℝ)+3) ≠ 0 := by positivity
  have h5 : (2*(n : ℝ)+5) ≠ 0 := by positivity
  field_simp
  simp only [mul_comm 2 x] at h
  apply mul_left_cancel₀ (show (2*(n : ℝ)+4) ≠ 0 by positivity)
  linear_combination -h

/-- The constant column includes the initial recurrence without an exceptional denominator. -/
theorem X_mul_shiftedJacobi_one_zero_zero :
    X*shiftedJacobi 1 0 0 =
      C (shiftedJacobiOneZeroUpper 0)*shiftedJacobi 1 0 1 +
      C (shiftedJacobiOneZeroDiag 0)*shiftedJacobi 1 0 0 := by
  apply Polynomial.funext
  intro x
  norm_num [eval_shiftedJacobi, jacobi_one, shiftedJacobiOneZeroUpper,
    shiftedJacobiOneZeroDiag]
  ring

end Polynomial
