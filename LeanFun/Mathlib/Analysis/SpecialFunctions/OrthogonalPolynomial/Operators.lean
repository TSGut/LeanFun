/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.RecurrenceCoefficients
public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap
public import LeanFun.Mathlib.LinearAlgebra.Matrix.Banded

/-! # Multiplication matrices in orthogonal polynomial bases
The polynomial operator is Mathlib's `LinearMap.mulLeft ℝ X`. Its matrix has
three diagonals, and its action on finitely supported coefficients is exact.
References: DLMF 18.2(iv); Olver--Townsend (2013), §2.
-/

public section
open MeasureTheory Module
namespace Polynomial.Sequence
variable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
  (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
  (hu : ∀ i, IsUnit (P i).leadingCoeff)
include hμ hpos hP

/-- Entries of multiplication in the positive-index columns (DLMF 18.2(iv)). -/
theorem IsOrthogonal.mul_matrix_succ (n i : ℕ) :
    (P.basis hu).toMatrix (fun j ↦ X * P j) i (n + 1) =
      (if i = n + 2 then P.recurrenceA (n + 1) else 0) +
      (if i = n + 1 then P.recurrenceB μ (n + 1) (Sequence.RecurrenceBInput.of _ _ _) else 0) +
      (if i = n then P.recurrenceC μ n (Sequence.RecurrenceCInput.of _ _ _) else 0) := by
  have hb (k : ℕ) : (P.basis hu).repr (P k) = Finsupp.single k 1 := by
    rw [← P.basis_eq_self hu k]
    exact (P.basis hu).repr_self k
  rw [Basis.toMatrix_apply, hP.three_term hμ hpos]
  simp [hb, Finsupp.single_apply, eq_comm]

/-- The initial multiplication column has two entries (DLMF 18.2(iv)). -/
theorem IsOrthogonal.mul_matrix_zero (i : ℕ) :
    (P.basis hu).toMatrix (fun j ↦ X * P j) i 0 =
      (if i = 1 then P.recurrenceA 0 else 0) +
      (if i = 0 then P.recurrenceB μ 0 (Sequence.RecurrenceBInput.of _ _ _) else 0) := by
  have hb (k : ℕ) : (P.basis hu).repr (P k) = Finsupp.single k 1 := by
    rw [← P.basis_eq_self hu k]
    exact (P.basis hu).repr_self k
  rw [Basis.toMatrix_apply, hP.two_term_zero hμ hpos]
  simp [hb, Finsupp.single_apply, eq_comm]

/-- Multiplication is tridiagonal for any nondegenerate orthogonal sequence,
without a support restriction on the measure (DLMF 18.2(iv)). -/
theorem IsOrthogonal.mul_matrix_isBanded :
    ((P.basis hu).toMatrix (fun j ↦ X * P j)).IsBanded 1 1 := by
  intro i j hij
  exact hP.basis_repr_X_mul_eq_zero hμ hpos hu hij

end Polynomial.Sequence
