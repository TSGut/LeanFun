/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Matrix.MaximalStep
import Mathlib.Tactic.Ring

/-! # First possible paths in a matrix sandwich
A left boundary edge, q interior steps and a right boundary edge cannot cross
more than q+2 levels. At equality every contributing edge is maximal.
Reference: finite matrix path expansion and Schur complements.
-/

public section
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Too few interior steps force a boundary-to-boundary sandwich to vanish. -/
theorem sum_mul_pow_mul_eq_zero_of_level_gap
    (K : Matrix ι ι ℝ) (F G : ι → ℝ) (level : ι → ℤ) (lo hi : ℤ)
    (hK : ∀ i j, level i + 1 < level j → K i j = 0)
    (hF : ∀ i, lo + 1 < level i → F i = 0)
    (hG : ∀ i, level i + 1 < hi → G i = 0)
    (q : ℕ) (hgap : lo + q + 2 < hi) :
    ∑ i, ∑ j, F i * (K ^ q) i j * G j = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hf : F i = 0
  · simp [hf]
  by_cases hg : G j = 0
  · simp [hg]
  have hfi : level i ≤ lo + 1 := by
    by_contra h
    exact hf (hF i (by omega))
  have hgj : hi ≤ level j + 1 := by
    by_contra h
    exact hg (hG j (by omega))
  rw [pow_apply_eq_zero_of_level_gap K level hK q i j (by omega)]
  simp

/-- At the first possible level gap, retaining only maximal boundary and
interior steps leaves the sandwich unchanged. -/
theorem sum_mul_pow_mul_eq_maximalStep
    (K : Matrix ι ι ℝ) (F G : ι → ℝ) (level : ι → ℤ) (lo hi : ℤ)
    (hK : ∀ i j, level i + 1 < level j → K i j = 0)
    (hF : ∀ i, lo + 1 < level i → F i = 0)
    (hG : ∀ i, level i + 1 < hi → G i = 0)
    (q : ℕ) (hgap : hi = lo + q + 2) :
    (∑ i, ∑ j, F i * (K ^ q) i j * G j) =
      ∑ i, ∑ j, (if level i = lo + 1 then F i else 0) *
        ((maximalStep K level) ^ q) i j * (if level j + 1 = hi then G j else 0) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hf : F i = 0
  · simp [hf]
  by_cases hg : G j = 0
  · simp [hg]
  have hfi : level i ≤ lo + 1 := by
    by_contra h
    exact hf (hF i (by omega))
  have hgj : hi ≤ level j + 1 := by
    by_contra h
    exact hg (hG j (by omega))
  by_cases hi' : level i = lo + 1
  · by_cases hj' : level j + 1 = hi
    · rw [ite_eq_left hi', ite_eq_left hj',
        pow_apply_eq_maximalStep K level hK q i j (by omega)]
    · rw [ite_eq_right hj', pow_apply_eq_zero_of_level_gap K level hK q i j (by omega)]
      simp
  · rw [ite_eq_right hi', pow_apply_eq_zero_of_level_gap K level hK q i j (by omega)]
    simp

/-- Diagonal signs telescope through both boundary edges and the interior power. -/
theorem sum_mul_pow_mul_sign_conjugate
    (K : Matrix ι ι ℝ) (F G s : ι → ℝ) (slo shi : ℝ)
    (hs : ∀ i, s i * s i = 1) (q : ℕ) :
    (∑ i, ∑ j, (slo * F i * s i) *
      ((Matrix.of (fun i j ↦ s i * K i j * s j)) ^ q) i j * (s j * G j * shi)) =
      slo * (∑ i, ∑ j, F i * (K ^ q) i j * G j) * shi := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_apply_sign_conjugate K s hs]
  calc
    _ = (slo * (F i * (K ^ q) i j * G j) * shi) * (s i * s i) * (s j * s j) := by ring
    _ = _ := by rw [hs, hs, mul_one, mul_one]

/-- Nonnegative factors and one strictly positive path give a positive sandwich. -/
theorem sum_mul_pow_mul_pos_of_positive_path
    (K : Matrix ι ι ℝ) (F G : ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hF : ∀ i, 0 ≤ F i) (hG : ∀ i, 0 ≤ G i)
    (q : ℕ) (p : ℕ → ι) (hfirst : 0 < F (p 0)) (hlast : 0 < G (p q))
    (hp : ∀ k < q, 0 < K (p k) (p (k + 1))) :
    0 < ∑ i, ∑ j, F i * (K ^ q) i j * G j := by
  have ht := mul_pos (mul_pos hfirst (pow_apply_pos_of_positive_path K hK q p hp)) hlast
  apply ht.trans_le
  calc
    _ ≤ ∑ j, F (p 0) * (K ^ q) (p 0) j * G j :=
      Finset.single_le_sum (fun j _ ↦ mul_nonneg
        (mul_nonneg (hF _) (pow_apply_nonneg hK q _ j)) (hG j)) (Finset.mem_univ _)
    _ ≤ ∑ i, ∑ j, F i * (K ^ q) i j * G j :=
      Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ mul_nonneg
        (mul_nonneg (hF i) (pow_apply_nonneg hK q i j)) (hG j))) (Finset.mem_univ _)

end Matrix
