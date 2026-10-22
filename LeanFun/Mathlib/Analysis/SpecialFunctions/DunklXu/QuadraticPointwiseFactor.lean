/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticFullFactor
public import LeanFun.Mathlib.Analysis.Matrix.InversePencilExceptions
public import LeanFun.Mathlib.LinearAlgebra.Matrix.GramFactorSectors

/-! # Pointwise full-factor obstruction from the disk inverse sandwich
This form applies at every nonexceptional parameter, beyond a neighborhood of
zero. Reference: Schur complements and complete parity-sector restriction.
-/

public section
open Matrix Filter
open scoped Topology
namespace MvPolynomial

/-- A nonzero inverse sandwich forces the distant entry at the same parameter. -/
theorem dunklXu_full_factor_entry_ne_zero_of_inverse {β : ℝ} (hβ : -1 < β)
    (u v : ℝ) (r : ℕ) (hr : 2 ≤ r)
    (t : Matrix.InvertiblePencilParameter (dunklXuInteriorMatrix hβ u v r))
    (ht : (t : ℝ) ≠ 0)
    (hinv : dunklXuInteriorFunctional hβ u v r
      (Matrix.inversePencil (dunklXuInteriorMatrix hβ u v r) t) ≠ 0) :
    ∀ {N : ℕ} {γ : Type}
      (R : Matrix (Fin N) (Fin N) ℝ) (sector : Fin N → γ)
      (e : DunklXuEvenInterior r ⊕ Fin (r + 1) → Fin N) (c : γ),
      R.IsUpperTriangular → (∀ i, R i i ≠ 0) →
      (∀ i j, sector i ≠ sector j → (R.transpose * R) i j = 0) →
      Function.Injective e → (∀ i, sector (e i) = c) →
      (∀ k, sector k = c → k ∈ Set.range e) →
      (∀ i j, e (Sum.inl i) < e (Sum.inr j)) → StrictMono (e ∘ Sum.inr) →
      (R.transpose * R).submatrix e e = dunklXuEvenGramPencil hβ u v t r →
      R (e (Sum.inr 0)) (e (Sum.inr (Fin.last r))) ≠ 0 := by
  intro N γ R sector e c hR hd hG he hc hcover hbefore hmono hP
  let A := R.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)
  let B := R.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
  let D := R.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
  have hblocks := hR.gram_sector_blocks hd sector hG e he c hc hcover hbefore
  change (R.transpose * R).submatrix e e =
    fromBlocks (A.transpose * A) (A.transpose * B) (B.transpose * A)
      (B.transpose * B + D.transpose * D) at hblocks
  have h := hblocks.symm.trans hP
  have hAA : A.transpose * A = 1 + (t : ℝ) • dunklXuInteriorMatrix hβ u v r := by
    ext i j
    exact congrArg (fun M ↦ M (Sum.inl i) (Sum.inl j)) h
  have hAB : A.transpose * B = (t : ℝ) • dunklXuQuadraticRightBlock hβ u v r := by
    ext i j
    exact congrArg (fun M ↦ M (Sum.inl i) (Sum.inr j)) h
  have hBA : B.transpose * A = (t : ℝ) • dunklXuQuadraticLeftBlock hβ u v r := by
    ext i j
    exact congrArg (fun M ↦ M (Sum.inr i) (Sum.inl j)) h
  have hDD : B.transpose * B + D.transpose * D =
      1 + (t : ℝ) • dunklXuQuadraticBoundaryBlock hβ u v r := by
    ext i j
    exact congrArg (fun M ↦ M (Sum.inr i) (Sum.inr j)) h
  apply Matrix.schur_gram_first_row_ne_zero_of_pencil A B D
    (dunklXuInteriorMatrix hβ u v r) (dunklXuQuadraticRightBlock hβ u v r)
    (dunklXuQuadraticLeftBlock hβ u v r) t ht
    (hR.isUnit_det_submatrix hd _ (he.comp Sum.inl_injective))
    (hR.submatrix_strictMono _ hmono) hAA hAB hBA (Fin.last r)
  · rw [hDD, Matrix.add_apply, Matrix.smul_apply,
      dunklXuQuadraticBoundaryBlock_first_last hβ u v r hr]
    have he : (0 : Fin (r + 1)) ≠ Fin.last r := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at this
      omega
    simp [he]
  · rw [← dunklXuInteriorFunctional_eq_sandwich]
    simpa only [Matrix.inversePencil_eq_inv] using hinv

/-- Only finitely many parameters can fail the full-factor implication. -/
theorem eventually_cofinite_dunklXu_full_factor_entry_ne_zero {β : ℝ} (hβ : -1 < β)
    (u v : ℝ) (hv : v ≠ 0) (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ t in Filter.cofinite, ∀ {N : ℕ} {γ : Type}
      (R : Matrix (Fin N) (Fin N) ℝ) (sector : Fin N → γ)
      (e : DunklXuEvenInterior r ⊕ Fin (r + 1) → Fin N) (c : γ),
      R.IsUpperTriangular → (∀ i, R i i ≠ 0) →
      (∀ i j, sector i ≠ sector j → (R.transpose * R) i j = 0) →
      Function.Injective e → (∀ i, sector (e i) = c) →
      (∀ k, sector k = c → k ∈ Set.range e) →
      (∀ i j, e (Sum.inl i) < e (Sum.inr j)) → StrictMono (e ∘ Sum.inr) →
      (R.transpose * R).submatrix e e = dunklXuEvenGramPencil hβ u v t r →
      R (e (Sum.inr 0)) (e (Sum.inr (Fin.last r))) ≠ 0 := by
  have hn := eventually_dunklXuInterior_inverse_ne_zero_of_vertical_ne_zero hβ u v hv r hr
  have he : ∃ t : ℝ, (dunklXuQuadraticLeftBlock hβ u v r *
      (1 + t • dunklXuInteriorMatrix hβ u v r)⁻¹ * dunklXuQuadraticRightBlock hβ u v r)
      0 (Fin.last r) ≠ 0 := by
    simpa only [dunklXuInteriorFunctional_eq_sandwich] using hn.exists
  have he' : ∃ t : Matrix.InvertiblePencilParameter (dunklXuInteriorMatrix hβ u v r),
      (dunklXuQuadraticLeftBlock hβ u v r *
        Matrix.inversePencil (dunklXuInteriorMatrix hβ u v r) t *
        dunklXuQuadraticRightBlock hβ u v r) 0 (Fin.last r) ≠ 0 := by
    obtain ⟨t, ht⟩ := he
    have hu : IsUnit (1 + t • dunklXuInteriorMatrix hβ u v r) := by
      by_contra hu
      apply ht
      rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ hu]
      simp
    exact ⟨⟨t, hu⟩, by simpa only [Matrix.inversePencil_eq_inv] using ht⟩
  have hc := Matrix.eventually_cofinite_inversePencil_sandwich_ne_zero
    (dunklXuInteriorMatrix hβ u v r) (dunklXuQuadraticLeftBlock hβ u v r)
    (dunklXuQuadraticRightBlock hβ u v r) 0 (Fin.last r) he'
  filter_upwards [hc, Filter.eventually_cofinite_ne (0 : ℝ)] with t ht ht0
  obtain ⟨hu, ht⟩ := ht
  exact dunklXu_full_factor_entry_ne_zero_of_inverse hβ u v r hr ⟨t, hu⟩ ht0
    (by simpa only [dunklXuInteriorFunctional_eq_sandwich] using ht)

end MvPolynomial
