/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Normalization
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Positive
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.ConnectionSupport
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.MeasureModification
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram

/-!
# The disk parameter connection as a positive triangular Gram factor

Finite sections use all polynomials through degree `N`. The explicit sparsity
and diagonal positivity identify the factor with Cholesky when indices are
ordered by total degree and then the inner index.
Reference: Gutleb–Olver–Slevinsky, Lemma 2.8; Dunkl–Xu, disk parameter raising.
-/

@[expose] public section
open Module Matrix
namespace MvPolynomial

/-- The normalized basis of a finite degree space has identity Gram matrix. -/
theorem integralGram_normalizedDunklXuDegreeBasis {β : ℝ} (hβ : -1 < β) (N : ℕ) :
    integralGram (dunklXuDiskMeasure β)
      (fun i => (normalizedDunklXuDegreeBasis hβ N i : MvPolynomial (Fin 2) ℝ)) = 1 := by
  classical
  ext i j
  simp only [integralGram, normalizedDunklXuDegreeBasis_apply,
    integralInner_normalizedDunklXuBasis, Matrix.one_apply]
  congr 1
  apply propext
  constructor
  · intro h
    apply Subtype.ext
    exact diskIndex_injective h
  · rintro rfl
    rfl

/-- The finite normalized connection for a unit increase of the disk parameter. -/
noncomputable def dunklXuRaisingMatrix {β : ℝ} (hβ : -1 < β) (N : ℕ) :
    Matrix {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
      {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ :=
  (normalizedDunklXuDegreeBasis (show -1 < β + 1 by linarith) N).toMatrix
    (normalizedDunklXuDegreeBasis hβ N)

/-- The normalized disk connection factors the raised-measure Gram matrix. -/
theorem integralGram_eq_dunklXuRaisingMatrix_transpose_mul {β : ℝ} (hβ : -1 < β)
    (N : ℕ) [Fintype {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}] :
    integralGram (dunklXuDiskMeasure (β + 1))
      (fun i => (normalizedDunklXuDegreeBasis hβ N i : MvPolynomial (Fin 2) ℝ))
      (hP := fun _ _ => (hasFiniteMoments_dunklXuDiskMeasure (by linarith)).integrable_mul _ _) =
      (dunklXuRaisingMatrix hβ N).transpose * dunklXuRaisingMatrix hβ N := by
  classical
  exact integralGram_eq_transpose_toMatrix_mul _
    (hasFiniteMoments_dunklXuDiskMeasure (by linarith))
    (hasPositiveDefiniteIntegral_dunklXuDiskMeasure (by linarith)) _ _
    (integralGram_normalizedDunklXuDegreeBasis (by linarith) N)

/-- Normalization acts by positive row and column scalings on the raw connection. -/
theorem dunklXuRaisingMatrix_apply {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    dunklXuRaisingMatrix hβ N i j =
      dunklXuNorm (β + 1) ⟨((i.1 0 + i.1 1), (i.1 1)), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩ *
        (dunklXuNorm β ⟨((j.1 0 + j.1 1), (j.1 1)), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩)⁻¹ *
        (dunklXuBasis (show -1 < β + 1 by linarith)).repr
          (dunklXuDisk β (j.1 0 + j.1 1) (j.1 1))
          ⟨i.1 0 + i.1 1, ⟨i.1 1, by omega⟩⟩ := by
  classical
  change (normalizedDunklXuDegreeBasis (show -1 < β + 1 by linarith) N).repr
    (normalizedDunklXuDegreeBasis hβ N j) i = _
  rw [basis_repr_eq_integralInner _ (hasFiniteMoments_dunklXuDiskMeasure (by linarith))
    _ (integralGram_normalizedDunklXuDegreeBasis (by linarith) N)]
  simp only [normalizedDunklXuDegreeBasis_apply]
  rw [← normalizedDunklXuBasis_repr_eq_integralInner, normalizedDunklXuBasis_repr,
    normalizedDunklXuBasis_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  ring

/-- The positive normalized factor has the four-term disk support. -/
theorem dunklXuRaisingMatrix_eq_zero {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N})
    (hout : ¬ ((i.1 0 + i.1 1 = j.1 0 + j.1 1 ∨
      i.1 0 + i.1 1 + 2 = j.1 0 + j.1 1) ∧
      (i.1 1 = j.1 1 ∨ i.1 1 + 2 = j.1 1))) :
    dunklXuRaisingMatrix hβ N i j = 0 := by
  rw [dunklXuRaisingMatrix_apply,
    dunklXuBasis_raise_repr_eq_zero hβ
      ⟨i.1 0 + i.1 1, ⟨i.1 1, by omega⟩⟩
      ⟨j.1 0 + j.1 1, ⟨j.1 1, by omega⟩⟩ hout, mul_zero]

/-- Every diagonal entry of the normalized disk factor is strictly positive. -/
theorem dunklXuRaisingMatrix_diag_pos {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (i : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    0 < dunklXuRaisingMatrix hβ N i i := by
  rw [dunklXuRaisingMatrix_apply]
  exact mul_pos (mul_pos (dunklXuNorm_pos (by linarith) _ _)
    (inv_pos.mpr (dunklXuNorm_pos hβ _ _))) (dunklXuBasis_raise_repr_self_pos hβ ⟨i.1 0 + i.1 1, ⟨i.1 1, by omega⟩⟩)

/-- The factor is upper triangular in degree order, with increasing inner index
within each degree block. -/
theorem dunklXuRaisingMatrix_eq_zero_of_order {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N})
    (hij : j.1 0 + j.1 1 < i.1 0 + i.1 1 ∨
      (j.1 0 + j.1 1 = i.1 0 + i.1 1 ∧ j.1 1 < i.1 1)) :
    dunklXuRaisingMatrix hβ N i j = 0 := by
  apply dunklXuRaisingMatrix_eq_zero hβ N i j
  omega

end MvPolynomial
