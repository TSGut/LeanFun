/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Positive triangular factors of Gram matrices

Gram–Schmidt supplies the positive-diagonal upper triangular connection factor
of an ordered real basis, independently of its interpretation as polynomials.
Reference: Gutleb–Olver–Slevinsky, measure modifications, Lemma 2.8.
-/

public section
open Module InnerProductSpace Matrix
open scoped InnerProductSpace
namespace InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

/-- The Gram–Schmidt diagonal coefficient is the norm of the residual vector. -/
theorem inner_gramSchmidtNormed_self (v : Fin n → E) (i : Fin n) :
    inner ℝ (gramSchmidtNormed ℝ v i) (v i) = ‖gramSchmidt ℝ v i‖ := by
  have hi : inner ℝ (gramSchmidt ℝ v i) (v i) = ‖gramSchmidt ℝ v i‖ ^ 2 := by
    rw [gramSchmidt_def'' ℝ v i]
    rw [inner_add_right, inner_sum]
    have hz : (∑ j ∈ Finset.Iio i,
        inner ℝ (gramSchmidt ℝ v i)
          ((inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖ ^ 2) •
            gramSchmidt ℝ v j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [inner_smul_right, gramSchmidt_orthogonal ℝ v
        (ne_of_gt (Finset.mem_Iio.mp hj)), mul_zero]
    simp only [RCLike.ofReal_real_eq_id, id_eq] at *
    rw [hz, add_zero, real_inner_self_eq_norm_sq]
  rw [gramSchmidtNormed, real_inner_smul_left, hi]
  by_cases h : gramSchmidt ℝ v i = 0
  · simp [h]
  have hn : ‖gramSchmidt ℝ v i‖ ≠ 0 := norm_ne_zero_iff.mpr h
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  field_simp

/-- Gram–Schmidt produces an orthonormal basis with positive upper triangular
coordinates for the supplied ordered basis. -/
theorem exists_orthonormalBasis_pos_upperTriangular (b : Basis (Fin n) ℝ E) :
    ∃ q : OrthonormalBasis (Fin n) ℝ E,
      (q.toBasis.toMatrix b).IsUpperTriangular ∧
        ∀ i, 0 < q.toBasis.toMatrix b i i := by
  let : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let hdim : finrank ℝ E = Fintype.card (Fin n) := Module.finrank_eq_card_basis b
  let q := gramSchmidtOrthonormalBasis (𝕜 := ℝ) hdim b
  refine ⟨q, gramSchmidtOrthonormalBasis_inv_isUpperTriangular hdim b, ?_⟩
  intro i
  change 0 < q.toBasis.repr (b i) i
  rw [q.coe_toBasis_repr_apply]
  dsimp [q]
  rw [OrthonormalBasis.repr_apply_apply,
    gramSchmidtOrthonormalBasis_apply hdim
      ((gramSchmidtNormed_orthonormal b.linearIndependent).ne_zero i),
    inner_gramSchmidtNormed_self]
  exact norm_pos_iff.mpr (gramSchmidt_ne_zero i b.linearIndependent)

/-- The Gram matrix is the transpose product of the coordinates in an
orthonormal basis, expressed using the existing basis change matrix. -/
theorem gram_eq_transpose_toMatrix_mul {ι : Type*} [Fintype ι]
    (q : OrthonormalBasis ι ℝ E) (v : ι → E) :
    gram ℝ v = (q.toBasis.toMatrix v).transpose * q.toBasis.toMatrix v := by
  have hR : q.toBasis.toMatrix v = Matrix.of (fun i j => q.repr (v j) i) := by
    ext i j
    exact q.coe_toBasis_repr_apply (v j) i
  rw [hR]
  simpa only [conjTranspose_eq_transpose_of_trivial] using gram_eq_conjTranspose_mul q v

/-- Gram–Schmidt gives a positive-diagonal triangular factor for the Gram
matrix of every finite ordered real basis. -/
theorem exists_pos_upperTriangular_gram_factor (b : Basis (Fin n) ℝ E) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ,
      R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧ gram ℝ b = R.transpose * R := by
  obtain ⟨q, ht, hp⟩ := exists_orthonormalBasis_pos_upperTriangular b
  exact ⟨q.toBasis.toMatrix b, ht, hp, gram_eq_transpose_toMatrix_mul q b⟩

end InnerProductSpace

namespace Matrix

/-- A real upper triangular Gram factor with positive diagonal is unique.
This is the finite uniqueness statement used for Cholesky measure conversion. -/
theorem eq_of_pos_upperTriangular_gram_eq {n : ℕ}
    {R S : Matrix (Fin n) (Fin n) ℝ}
    (hR : R.IsUpperTriangular) (hS : S.IsUpperTriangular)
    (hRp : ∀ i, 0 < R i i) (hSp : ∀ i, 0 < S i i)
    (hgram : R.transpose * R = S.transpose * S) : R = S := by
  have hrow : ∀ i, ∀ j, R i j = S i j := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hprod (j : Fin n) : R i i * R i j = S i i * S i j := by
        have heq := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hgram
        simp only [mul_apply, transpose_apply] at heq
        have hsum : (∑ k, (R k i * R k j - S k i * S k j)) =
            R i i * R i j - S i i * S i j := by
          apply Finset.sum_eq_single i
          · intro k _ hki
            rcases lt_or_gt_of_ne hki with hk | hk
            · rw [ih k hk i, ih k hk j, sub_self]
            · rw [hR hk, hS hk, zero_mul, zero_mul, sub_self]
          · simp
        rw [Finset.sum_sub_distrib, heq, sub_self] at hsum
        exact sub_eq_zero.mp hsum.symm
      have hd : R i i = S i i := by
        have hsquare := hprod i
        nlinarith [hRp i, hSp i]
      intro j
      have hj := hprod j
      rw [← hd] at hj
      exact mul_left_cancel₀ (ne_of_gt (hRp i)) hj
  exact Matrix.ext hrow

/-- Leading principal sections of an upper triangular Gram factor are exact;
no rows outside the section contribute to the restricted Gram matrix. -/
theorem IsUpperTriangular.transpose_mul_self_principal {n m : ℕ}
    {R : Matrix (Fin (n + m)) (Fin (n + m)) ℝ} (hR : R.IsUpperTriangular) :
    (R.transpose * R).submatrix (Fin.castAdd m) (Fin.castAdd m) =
      (R.submatrix (Fin.castAdd m) (Fin.castAdd m)).transpose *
        R.submatrix (Fin.castAdd m) (Fin.castAdd m) := by
  ext i j
  simp only [submatrix_apply, mul_apply, transpose_apply, Fin.sum_univ_add]
  have hz : (∑ k : Fin m, R (Fin.natAdd n k) (Fin.castAdd m i) *
      R (Fin.natAdd n k) (Fin.castAdd m j)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hi : Fin.castAdd m i < Fin.natAdd n k := by
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      omega
    exact mul_eq_zero_of_left (hR hi) _
  rw [hz, add_zero]

/-- Positive upper triangular factors agree on leading principal sections
whenever their Gram matrices agree there. -/
theorem eq_principal_of_pos_upperTriangular_gram_eq {n m : ℕ}
    {R : Matrix (Fin (n + m)) (Fin (n + m)) ℝ}
    {S : Matrix (Fin n) (Fin n) ℝ}
    (hR : R.IsUpperTriangular) (hS : S.IsUpperTriangular)
    (hRp : ∀ i, 0 < R i i) (hSp : ∀ i, 0 < S i i)
    (hgram : (R.transpose * R).submatrix (Fin.castAdd m) (Fin.castAdd m) =
      S.transpose * S) : R.submatrix (Fin.castAdd m) (Fin.castAdd m) = S := by
  have ht : (R.submatrix (Fin.castAdd m) (Fin.castAdd m)).IsUpperTriangular := by
    intro i j hji
    exact hR (by simpa only [id_eq, Fin.lt_def, Fin.val_castAdd] using hji)
  exact eq_of_pos_upperTriangular_gram_eq ht hS (fun i => hRp _) hSp
    (hR.transpose_mul_self_principal.symm.trans hgram)

end Matrix
