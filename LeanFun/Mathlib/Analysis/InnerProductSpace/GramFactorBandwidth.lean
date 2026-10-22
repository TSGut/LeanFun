/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.GramSchmidtFactor

/-!
# Degree-block bandwidth of triangular Gram factors

A positive triangular Gram factor preserves the upper degree-block bandwidth
of its Gram matrix. This gives no additional zeros inside the permitted blocks.

Reference: Gutleb–Olver–Slevinsky, measure modifications, Lemma 2.8 and Section 5.
-/

public section
namespace Matrix

/-- A nonzero-diagonal upper triangular Gram factor preserves degree-block
bandwidth, for a monotone degree labelling of the scalar ordering. -/
theorem IsUpperTriangular.eq_zero_of_transpose_mul_self_degree_band {n : ℕ}
    {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsUpperTriangular)
    (hdiag : ∀ i, R i i ≠ 0) (degree : Fin n → ℕ) (hdegree : Monotone degree)
    (d : ℕ) (hband : ∀ i j, degree i + d < degree j → (R.transpose * R) i j = 0) :
    ∀ i j, degree i + d < degree j → R i j = 0 := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro j hij
    have hs : (R.transpose * R) i j = R i i * R i j := by
      rw [mul_apply]
      apply Finset.sum_eq_single i
      · intro k _ hki
        simp only [transpose_apply]
        rcases lt_or_gt_of_ne hki with hk | hk
        · have hj : degree k + d < degree j :=
            lt_of_le_of_lt (Nat.add_le_add_right (hdegree hk.le) d) hij
          rw [ih k hk j hj, mul_zero]
        · exact mul_eq_zero_of_left (hR hk) _
      · simp
    exact (mul_eq_zero.mp (hs.symm.trans (hband i j hij))).resolve_left (hdiag i)

end Matrix
