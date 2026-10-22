/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Matrix.CholeskyLU
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Exact minors as necessary conditions for elimination zeros

A selected row of an upper factor cannot vanish unless the corresponding
bordered minor of the original matrix vanishes. This gives finite algebraic
obstructions to proposed Cholesky/LU support, without numerical thresholds.
Reference: Gutleb–Olver–Slevinsky, measure modification through factorizations.
-/

public section
namespace Matrix
variable {n m : ℕ}

/-- Restricting leading rows of a lower-triangular product needs no trailing summands. -/
theorem lowerTriangular_mul_submatrix (L U : Matrix (Fin (n+m)) (Fin (n+m)) ℝ)
    (hL : L.transpose.IsUpperTriangular) (col : Fin n → Fin (n+m)) :
    (L*U).submatrix (Fin.castAdd m) col =
      L.submatrix (Fin.castAdd m) (Fin.castAdd m) * U.submatrix (Fin.castAdd m) col := by
  ext i j
  simp only [submatrix_apply, mul_apply, Fin.sum_univ_add]
  have hz : (∑ k : Fin m, L (Fin.castAdd m i) (Fin.natAdd n k)*U (Fin.natAdd n k) (col j)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hi : Fin.castAdd m i < Fin.natAdd n k := by
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      omega
    have he : L (Fin.castAdd m i) (Fin.natAdd n k) = 0 := hL hi
    rw [he, zero_mul]
  rw [hz, add_zero]

/-- A zero selected upper-factor row forces the corresponding bordered minor to vanish. -/
theorem det_submatrix_eq_zero_of_lower_factorization
    (W L U : Matrix (Fin (n+m)) (Fin (n+m)) ℝ)
    (hW : W = L*U) (hL : L.transpose.IsUpperTriangular)
    (col : Fin n → Fin (n+m)) (i : Fin n)
    (hz : ∀ j, U (Fin.castAdd m i) (col j) = 0) :
    (W.submatrix (Fin.castAdd m) col).det = 0 := by
  rw [hW, lowerTriangular_mul_submatrix L U hL col, det_mul,
    det_eq_zero_of_row_eq_zero (A := U.submatrix (Fin.castAdd m) col) i hz, mul_zero]

end Matrix
