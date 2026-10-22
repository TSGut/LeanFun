/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Orthogonality
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Operators

import Mathlib.Tactic.Linarith

/-! # Gegenbauer operator bases in the orthogonality range
The polynomial bases retain the original Gegenbauer normalisation. All operator
formulas apply also to -1/2 < λ < 0. References: DLMF 18.9.1, 18.9.7, 18.9.19;
Olver--Townsend (2013).
-/

public section
open Module
namespace Polynomial
variable {lam : ℝ} (hlam : -(1 / 2) < lam) (hzero : lam ≠ 0)

/-- The Gegenbauer basis of polynomials, without Hilbert-space normalisation
(DLMF Table 18.3.1). -/
@[expose] noncomputable def gegenbauerBasis : Basis ℕ ℝ ℝ[X] :=
  (gegenbauerSequence hlam hzero).basis (fun n ↦ isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr ((gegenbauerSequence hlam hzero).ne_zero n)))

/-- The basis vectors are the independent Gegenbauer polynomials (DLMF Table 18.3.1). -/
@[simp] theorem gegenbauerBasis_apply (n : ℕ) :
    gegenbauerBasis hlam hzero n = gegenbauer lam n := by
  simp [gegenbauerBasis]

/-- Multiplication is tridiagonal throughout the nondegenerate range (DLMF 18.9.1). -/
theorem gegenbauerBasis_mul_isBanded :
    ((gegenbauerBasis hlam hzero).toMatrix (fun j ↦ X * gegenbauer lam j)).IsBanded 1 1 := by
  apply gegenbauer_mul_matrix_isBanded lam _ (gegenbauerBasis_apply hlam hzero) hzero
  intro n
  exact ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- Differentiation into parameter λ+1 has one upper diagonal (DLMF 18.9.19). -/
theorem gegenbauerBasis_derivative_isBanded :
    ((gegenbauerBasis (by linarith : -(1 / 2) < lam + 1)
      (ne_of_gt (by linarith : 0 < lam + 1))).toMatrix
        (fun j ↦ derivative (gegenbauer lam j))).IsBanded 0 1 := by
  apply gegenbauer_derivative_matrix_isBanded
  exact gegenbauerBasis_apply _ _

/-- Conversion into parameter λ+1 has upper bandwidth two (DLMF 18.9.7). -/
theorem gegenbauerBasis_conversion_isBanded :
    ((gegenbauerBasis (by linarith : -(1 / 2) < lam + 1)
      (ne_of_gt (by linarith : 0 < lam + 1))).toMatrix
        (gegenbauer lam)).IsBanded 0 2 := by
  apply gegenbauer_conversion_matrix_isBanded lam _ (gegenbauerBasis_apply _ _)
  intro n
  exact ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) n])

end Polynomial
