/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Orthogonality
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Operators

import Mathlib.Tactic.Linarith

/-! # Jacobi operator bases in the orthogonality range
For α, β > -1 all the polynomial bases exist and every conversion and
multiplication denominator is nonzero. These are algebraic bases of polynomials,
not the normalised Hilbert bases of weighted L².
References: DLMF 18.9.1--2, 18.9.5, 18.9.15; Olver--Townsend (2013).
-/

public section
open Module
namespace Polynomial
variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)

/-- The Jacobi basis of the polynomial space in its original normalisation
(DLMF Table 18.3.1). -/
@[expose] noncomputable def jacobiBasis : Basis ℕ ℝ ℝ[X] :=
  (jacobiSequence hα hβ).basis (fun n ↦
    (jacobiSequence hα hβ).isUnit_leadingCoeff n)

/-- The basis vectors are the independent Jacobi polynomials (DLMF Table 18.3.1). -/
@[simp] theorem jacobiBasis_apply (n : ℕ) : jacobiBasis hα hβ n = jacobi α β n := by
  simp [jacobiBasis]

/-- Multiplication by X is tridiagonal throughout the orthogonality range
(DLMF 18.9.1--2). -/
theorem jacobiBasis_mul_isBanded :
    ((jacobiBasis hα hβ).toMatrix (fun j ↦ X * jacobi α β j)).IsBanded 1 1 := by
  apply jacobi_mul_matrix_isBanded α β _ (jacobiBasis_apply hα hβ)
  · exact ne_of_gt (by linarith)
  · intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact mul_ne_zero (mul_ne_zero (ne_of_gt (by linarith))
      (ne_of_gt (by linarith))) (ne_of_gt (by linarith))

/-- Differentiation into parameters (α+1, β+1) has one upper diagonal
(DLMF 18.9.15). -/
theorem jacobiBasis_derivative_isBanded :
    ((jacobiBasis (by linarith : -1 < α + 1) (by linarith : -1 < β + 1)).toMatrix
      (fun j ↦ derivative (jacobi α β j))).IsBanded 0 1 := by
  apply jacobi_derivative_matrix_isBanded
  exact jacobiBasis_apply _ _

/-- Raising α is upper bidiagonal throughout the orthogonality range (DLMF 18.9.5). -/
theorem jacobiBasis_raise_alpha_isBanded :
    ((jacobiBasis (by linarith : -1 < α + 1) hβ).toMatrix
      (jacobi α β)).IsBanded 0 1 := by
  apply jacobi_raise_alpha_matrix_isBanded α β _ (jacobiBasis_apply _ _)
  intro n
  exact ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- Raising β is upper bidiagonal throughout the orthogonality range (DLMF 18.9.5). -/
theorem jacobiBasis_raise_beta_isBanded :
    ((jacobiBasis hα (by linarith : -1 < β + 1)).toMatrix
      (jacobi α β)).IsBanded 0 1 := by
  apply jacobi_raise_beta_matrix_isBanded α β _ (jacobiBasis_apply _ _)
  intro n
  exact ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) n])

end Polynomial
