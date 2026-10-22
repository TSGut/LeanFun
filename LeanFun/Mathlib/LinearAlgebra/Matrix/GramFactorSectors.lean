/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.GramSchmidtFactor
public import Mathlib.Data.Matrix.Block

/-! # Orthogonal sectors of a triangular Gram factor
An upper triangular factor with nonzero diagonal inherits exact sector zeros
from its Gram matrix, even when the sector indices are interleaved.
Reference: Cholesky elimination and orthogonal parity decompositions.
-/

public section
namespace Matrix

/-- A triangular Gram factor cannot couple orthogonal sectors. No contiguous
block ordering is required for the sector labels. -/
theorem IsUpperTriangular.apply_eq_zero_of_gram_sectors {n : ℕ} {γ : Type*}
    {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsUpperTriangular)
    (hd : ∀ i, R i i ≠ 0) (sector : Fin n → γ)
    (hG : ∀ i j, sector i ≠ sector j → (R.transpose * R) i j = 0)
    (i j : Fin n) (hij : sector i ≠ sector j) : R i j = 0 := by
  classical
  have hrow (m : ℕ) : ∀ i : Fin n, i.val = m → ∀ j, sector i ≠ sector j → R i j = 0 := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i hi j hij
      have hs : (R.transpose * R) i j = R i i * R i j := by
        rw [mul_apply]
        apply Finset.sum_eq_single i
        · intro k _ hki
          change R k i * R k j = 0
          by_cases hk : k < i
          · by_cases hsector : sector k = sector i
            · rw [ih k.val (by omega) k rfl j (by simpa [hsector] using hij), mul_zero]
            · rw [ih k.val (by omega) k rfl i hsector, zero_mul]
          · rw [hR (by omega : i < k), zero_mul]
        · simp
      exact (mul_eq_zero.mp (hs.symm.trans (hG i j hij))).resolve_left (hd i)
  exact hrow i.val i rfl j hij

/-- Restricting to a complete sector commutes with taking the Gram matrix,
even when the sector's indices are interleaved with other sectors. -/
theorem IsUpperTriangular.transpose_mul_self_sector {n : ℕ} {ι γ : Type*} [Fintype ι]
    {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsUpperTriangular)
    (hd : ∀ i, R i i ≠ 0) (sector : Fin n → γ)
    (hG : ∀ i j, sector i ≠ sector j → (R.transpose * R) i j = 0)
    (e : ι → Fin n) (he : Function.Injective e) (c : γ)
    (hc : ∀ i, sector (e i) = c) (hcover : ∀ k, sector k = c → k ∈ Set.range e) :
    (R.transpose * R).submatrix e e = (R.submatrix e e).transpose * R.submatrix e e := by
  ext i j
  simp only [submatrix_apply, mul_apply, transpose_apply]
  symm
  apply Fintype.sum_of_injective e he
  · intro k hk
    have hki : sector k ≠ sector (e i) := by
      rw [hc]
      exact fun h ↦ hk (hcover k h)
    rw [hR.apply_eq_zero_of_gram_sectors hd sector hG k (e i) hki, zero_mul]
  · intro k
    rfl

/-- Increasing enumeration of a sector preserves triangularity of the factor. -/
theorem IsUpperTriangular.submatrix_strictMono {n m : ℕ}
    {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsUpperTriangular)
    (e : Fin m → Fin n) (he : StrictMono e) : (R.submatrix e e).IsUpperTriangular := by
  intro i j hij
  exact hR (he hij)

/-- Any principal submatrix of a triangular matrix with nonzero diagonal is
invertible, even if the index enumeration has not been sorted. -/
theorem IsUpperTriangular.isUnit_det_submatrix {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {R : Matrix (Fin n) (Fin n) ℝ}
    (hR : R.IsUpperTriangular) (hd : ∀ i, R i i ≠ 0)
    (e : ι → Fin n) (he : Function.Injective e) : IsUnit (R.submatrix e e).det := by
  let : LinearOrder ι := LinearOrder.lift' e he
  have ht : (R.submatrix e e).IsUpperTriangular := fun _ _ hij ↦ hR hij
  rw [det_of_isUpperTriangular ht, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hd (e i))

/-- A complete orthogonal sector split into earlier and later indices has the
usual upper block Gram formula, independently of interleaving outside the sector. -/
theorem IsUpperTriangular.gram_sector_blocks {n : ℕ} {ι κ γ : Type*}
    [Fintype ι] [Fintype κ] {R : Matrix (Fin n) (Fin n) ℝ}
    (hR : R.IsUpperTriangular) (hd : ∀ i, R i i ≠ 0) (sector : Fin n → γ)
    (hG : ∀ i j, sector i ≠ sector j → (R.transpose * R) i j = 0)
    (e : ι ⊕ κ → Fin n) (he : Function.Injective e) (c : γ)
    (hc : ∀ i, sector (e i) = c) (hcover : ∀ k, sector k = c → k ∈ Set.range e)
    (hbefore : ∀ i j, e (Sum.inl i) < e (Sum.inr j)) :
    let A := R.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)
    let B := R.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
    let D := R.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
    (R.transpose * R).submatrix e e =
      fromBlocks (A.transpose * A) (A.transpose * B) (B.transpose * A)
        (B.transpose * B + D.transpose * D) := by
  classical
  dsimp only
  rw [hR.transpose_mul_self_sector hd sector hG e he c hc hcover]
  have hs : R.submatrix e e = fromBlocks
      (R.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl))
      (R.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)) 0
      (R.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := by
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => exact hR (hbefore j i)
      | inr j => rfl
  rw [hs, fromBlocks_transpose, fromBlocks_multiply]
  simp

end Matrix
