/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.GramSchmidtFactor
import Mathlib.Tactic.FieldSimp

/-!
# Unpivoted LU and diagonally normalized Cholesky

A positive triangular Gram factor gives a unit-lower/upper factorization after
diagonal similarity. The upper factor has exactly the same zeros.
Reference: Gutleb–Olver–Slevinsky, polynomial measure modifications.
-/

public section
namespace Matrix
variable {n : ℕ}

/-- Diagonal similarity and Cholesky give an unpivoted LU factorization whose
upper factor has exactly the Cholesky support. -/
theorem exists_lu_of_diagonal_gram_factor (W C : Matrix (Fin n) (Fin n) ℝ)
    (D : Fin n → ℝ) (hD : ∀ i, D i ≠ 0)
    (hC : C.IsUpperTriangular) (hc : ∀ i, C i i ≠ 0)
    (hg : C.transpose * C = diagonal D * W * diagonal (fun i => (D i)⁻¹)) :
    ∃ L U : Matrix (Fin n) (Fin n) ℝ,
      L.transpose.IsUpperTriangular ∧ (∀ i, L i i = 1) ∧ U.IsUpperTriangular ∧
      W = L * U ∧ (∀ i j, U i j = (D i)⁻¹ * C i i * C i j * D j) ∧
      (∀ i j, U i j = 0 ↔ C i j = 0) := by
  let L : Matrix (Fin n) (Fin n) ℝ := fun i j => (D i)⁻¹ * C j i * (C j j)⁻¹ * D j
  let U : Matrix (Fin n) (Fin n) ℝ := fun i j => (D i)⁻¹ * C i i * C i j * D j
  refine ⟨L, U, ?_, ?_, ?_, ?_, fun _ _ => rfl, ?_⟩
  · intro i j hij
    change (D j)⁻¹ * C i j * (C i i)⁻¹ * D i = 0
    rw [hC hij]
    ring
  · intro i
    dsimp [L]
    field_simp [hD, hc]
  · intro i j hij
    change (D i)⁻¹ * C i i * C i j * D j = 0
    rw [hC hij]
    ring
  · ext i j
    have hg' := congrArg (fun M => M i j) hg
    simp only [diagonal_mul, mul_diagonal] at hg'
    simp only [mul_apply, transpose_apply] at hg'
    rw [mul_apply]
    have hs : (∑ k, L i k * U k j) = (D i)⁻¹ * (∑ k, C k i * C k j) * D j := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [L, U]
      field_simp [hD, hc]
    rw [hs, hg']
    field_simp [hD, hc]
  · intro i j
    dsimp [U]
    simp only [mul_eq_zero, inv_eq_zero, hD, hc, false_or, or_false]

/-- Unpivoted LU with unit lower diagonal and nonzero pivots is unique. -/
theorem unitLower_upper_factorization_unique
    (L U L' U' : Matrix (Fin n) (Fin n) ℝ)
    (hL : L.transpose.IsUpperTriangular) (hL' : L'.transpose.IsUpperTriangular)
    (hU : U.IsUpperTriangular) (hU' : U'.IsUpperTriangular)
    (hd : ∀ i, L i i = 1) (hd' : ∀ i, L' i i = 1)
    (hu : ∀ i, U i i ≠ 0) (he : L * U = L' * U') : L = L' ∧ U = U' := by
  have hall (i : Fin n) : (∀ j, U i j = U' i j) ∧ (∀ j, L j i = L' j i) := by
    induction i using WellFoundedLT.induction with | ind i ih
    have hrow (j : Fin n) : U i j = U' i j := by
      have h := congrArg (fun M => M i j) he
      simp only [mul_apply] at h
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hd, hd', one_mul, one_mul] at h
      have hs : (∑ k ∈ Finset.univ.erase i, L i k * U k j) =
          ∑ k ∈ Finset.univ.erase i, L' i k * U' k j := by
        apply Finset.sum_congr rfl
        intro k hk
        have hki := (Finset.mem_erase.mp hk).1
        rcases lt_or_gt_of_ne hki with hlt | hgt
        · rw [(ih k hlt).1 j, (ih k hlt).2 i]
        · rw [show L i k = 0 from hL hgt, show L' i k = 0 from hL' hgt, zero_mul, zero_mul]
      rw [hs] at h
      exact add_right_cancel h
    refine ⟨hrow, ?_⟩
    intro j
    have h := congrArg (fun M => M j i) he
    simp only [mul_apply] at h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    have hs : (∑ k ∈ Finset.univ.erase i, L j k * U k i) =
        ∑ k ∈ Finset.univ.erase i, L' j k * U' k i := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki := (Finset.mem_erase.mp hk).1
      rcases lt_or_gt_of_ne hki with hlt | hgt
      · rw [(ih k hlt).1 i, (ih k hlt).2 j]
      · rw [hU hgt, hU' hgt, mul_zero, mul_zero]
    rw [hs, ← hrow i] at h
    exact mul_right_cancel₀ (hu i) (add_right_cancel h)
  exact ⟨by ext i j; exact (hall j).2 i, by ext i j; exact (hall i).1 j⟩

/-- Any exact unpivoted LU of the diagonally normalized Gram matrix has the
same upper-factor zeros as Cholesky, with the precise diagonal scaling. -/
theorem upper_eq_of_diagonal_gram_factor
    (W C L U : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ)
    (hD : ∀ i, D i ≠ 0) (hC : C.IsUpperTriangular) (hc : ∀ i, C i i ≠ 0)
    (hg : C.transpose * C = diagonal D * W * diagonal (fun i => (D i)⁻¹))
    (hL : L.transpose.IsUpperTriangular) (hd : ∀ i, L i i = 1)
    (hU : U.IsUpperTriangular) (hLU : W = L * U) :
    (∀ i j, U i j = (D i)⁻¹ * C i i * C i j * D j) ∧
      (∀ i j, U i j = 0 ↔ C i j = 0) := by
  obtain ⟨L', U', hL', hd', hU', hLU', hf, hz⟩ :=
    exists_lu_of_diagonal_gram_factor W C D hD hC hc hg
  have hu' : ∀ i, U' i i ≠ 0 := fun i => by
    intro h
    exact hc i ((hz i i).mp h)
  have he := unitLower_upper_factorization_unique L' U' L U hL' hL hU' hU hd' hd hu'
    (hLU'.symm.trans hLU)
  rw [he.2] at hf hz
  exact ⟨hf, hz⟩

end Matrix
