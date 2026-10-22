/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Connection

/-! # Signs of Cartesian disk parameter raising
The four explicit coefficients have signs `+,-,+,-` whenever the corresponding
lower degrees exist. Reference: Dunkl–Xu, disk families; DLMF 18.9.
-/

public section
open Polynomial
namespace MvPolynomial

private theorem outerParameter_gt_neg_one {β : ℝ} (hβ : -1 < β) (k : ℕ) :
    -1 < β + k + 1 / 2 := by
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

/-- The diagonal coefficient is positive for the full disk parameter range. -/
theorem dunklXuDiskRaiseA_pos {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    0 < dunklXuDiskRaiseA β n k :=
  mul_pos (jacobiSymmetricRaiseA_pos hβ k)
    (jacobiSymmetricRaiseA_pos (outerParameter_gt_neg_one hβ k) (n - k))

/-- The fixed-inner-index, lower-total-degree coefficient is nonpositive. -/
theorem dunklXuDiskRaiseB_nonpos {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    dunklXuDiskRaiseB β n k ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (jacobiSymmetricRaiseA_pos hβ k).le
    (jacobiSymmetricRaiseB_nonpos (outerParameter_gt_neg_one hβ k) (n - k))

/-- The fixed-inner-index coefficient is negative when its outer degree exists. -/
theorem dunklXuDiskRaiseB_neg {β : ℝ} (hβ : -1 < β) {n k : ℕ} (hn : k + 2 ≤ n) :
    dunklXuDiskRaiseB β n k < 0 := by
  unfold dunklXuDiskRaiseB
  apply mul_neg_of_pos_of_neg (jacobiSymmetricRaiseA_pos hβ k)
  have he : n - k = (n - k - 2) + 2 := by omega
  simpa only [← he] using jacobiSymmetricRaiseB_neg (outerParameter_gt_neg_one hβ k) (n-k-2)

/-- The fixed-total-degree coefficient is positive when the inner degree is at least two. -/
theorem dunklXuDiskRaiseC_pos {β : ℝ} (hβ : -1 < β) (n : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    0 < dunklXuDiskRaiseC β n k := by
  rw [dunklXuDiskRaiseC, dite_eq_right (by omega : ¬ k < 2)]
  apply mul_pos_of_neg_of_neg
  · have he : k = (k - 2) + 2 := by omega
    simpa only [← he] using jacobiSymmetricRaiseB_neg hβ (k-2)
  · apply jacobiSymmetricLowerA_neg
    have := Nat.cast_nonneg (α := ℝ) (k - 2)
    linarith

/-- Lowering both indices gives a negative coefficient when the inner degree is at least two. -/
theorem dunklXuDiskRaiseD_neg {β : ℝ} (hβ : -1 < β) (n : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    dunklXuDiskRaiseD β n k < 0 := by
  rw [dunklXuDiskRaiseD, dite_eq_right (by omega : ¬ k < 2)]
  apply mul_neg_of_neg_of_pos
  · have he : k = (k - 2) + 2 := by omega
    simpa only [← he] using jacobiSymmetricRaiseB_neg hβ (k-2)
  · apply jacobiSymmetricLowerB_pos
    have := Nat.cast_nonneg (α := ℝ) (k - 2)
    linarith

end MvPolynomial
