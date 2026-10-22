/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.GramSchmidtFactor
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
/-!
# Schur complements of triangular Gram factors

Eliminating the leading block leaves the Gram matrix of the trailing factor.
Its first row detects the corresponding Cholesky entries exactly.
Reference: Gutleb–Olver–Slevinsky, measure modification through factorizations.
-/

public section
namespace Matrix
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The Schur complement of an upper block Gram factor is the trailing Gram matrix. -/
theorem schur_gram_upper_blocks (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (D : Matrix κ κ ℝ) (hA : IsUnit A.det) :
    (B.transpose*B+D.transpose*D) -
      (B.transpose*A)*(A.transpose*A)⁻¹*(A.transpose*B) = D.transpose*D := by
  rw [mul_inv_rev]
  have he : (B.transpose*A)*(A⁻¹*A.transpose⁻¹)*(A.transpose*B) = B.transpose*B := by
    simp only [← Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_right A _ hA,
      nonsing_inv_mul_cancel_right A.transpose _ (isUnit_det_transpose A hA)]
  rw [he]
  abel

/-- The first Gram row of an upper triangular matrix is its first row times the first pivot. -/
theorem IsUpperTriangular.transpose_mul_self_first_row {n : ℕ}
    {D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hD : D.IsUpperTriangular) (j : Fin (n+1)) :
    (D.transpose*D) 0 j = D 0 0 * D 0 j := by
  rw [mul_apply]
  apply Finset.sum_eq_single 0
  · intro k _ hk
    change D k 0 * D k j = 0
    rw [hD (Fin.pos_iff_ne_zero.mpr hk), zero_mul]
  · simp

/-- A nonzero first pivot makes the Schur entry and the factor entry vanish together. -/
theorem schur_gram_first_row_ne_zero_iff {n : ℕ}
    (A : Matrix ι ι ℝ) (B : Matrix ι (Fin (n+1)) ℝ)
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : IsUnit A.det) (hD : D.IsUpperTriangular) (hd : D 0 0 ≠ 0)
    (j : Fin (n+1)) :
    ((B.transpose*B+D.transpose*D) -
      (B.transpose*A)*(A.transpose*A)⁻¹*(A.transpose*B)) 0 j ≠ 0 ↔ D 0 j ≠ 0 := by
  rw [schur_gram_upper_blocks A B D hA, hD.transpose_mul_self_first_row j]
  simp [hd]
/-- For affine leading and off-diagonal blocks, a zero original entry leaves the inverse sandwich. -/
theorem schur_gram_first_row_eq_of_pencil {n : ℕ}
    (A : Matrix ι ι ℝ) (B : Matrix ι (Fin (n+1)) ℝ)
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (K : Matrix ι ι ℝ) (E : Matrix ι (Fin (n+1)) ℝ)
    (F : Matrix (Fin (n+1)) ι ℝ) (t : ℝ)
    (hA : IsUnit A.det) (hD : D.IsUpperTriangular)
    (hAA : A.transpose*A = 1+t • K) (hAB : A.transpose*B = t • E)
    (hBA : B.transpose*A = t • F) (j : Fin (n+1))
    (hij : (B.transpose*B+D.transpose*D) 0 j = 0) :
    D 0 0 * D 0 j = -t^2 * (F*(1+t • K)⁻¹*E) 0 j := by
  have he := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M 0 j)
    (schur_gram_upper_blocks A B D hA)
  rw [hAA, hAB, hBA, sub_apply, hij, hD.transpose_mul_self_first_row] at he
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_apply, smul_eq_mul] at he
  nlinarith [he]

/-- A nonzero inverse sandwich forces the corresponding Cholesky entry to be nonzero. -/
theorem schur_gram_first_row_ne_zero_of_pencil {n : ℕ}
    (A : Matrix ι ι ℝ) (B : Matrix ι (Fin (n+1)) ℝ)
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (K : Matrix ι ι ℝ) (E : Matrix ι (Fin (n+1)) ℝ)
    (F : Matrix (Fin (n+1)) ι ℝ) (t : ℝ) (ht : t ≠ 0)
    (hA : IsUnit A.det) (hD : D.IsUpperTriangular)
    (hAA : A.transpose*A = 1+t • K) (hAB : A.transpose*B = t • E)
    (hBA : B.transpose*A = t • F) (j : Fin (n+1))
    (hij : (B.transpose*B+D.transpose*D) 0 j = 0)
    (hf : (F*(1+t • K)⁻¹*E) 0 j ≠ 0) : D 0 j ≠ 0 := by
  have he := schur_gram_first_row_eq_of_pencil A B D K E F t hA hD hAA hAB hBA j hij
  intro hd
  rw [hd, mul_zero] at he
  exact (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ ht)) hf) he.symm

end Matrix
