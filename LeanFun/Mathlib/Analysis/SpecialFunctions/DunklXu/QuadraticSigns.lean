/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticPairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.SymmetricDoublePairing

/-! # Strict maximal-inner-step signs for disk multiplication
For an increase of two in the inner index, total-degree changes +2,0,-2
have signs +,-,+. The degree-zero and degree-one outer cases are retained.
Reference: Dunkl--Xu, Cartesian disk construction; DLMF 18.9.
-/

public section
open Polynomial
namespace MvPolynomial

private theorem outerParameter_pos {β : ℝ} (hβ : -1 < β) (k : ℕ) :
    -1 < β + k + 1 / 2 := by
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

private theorem shifted_outerParameter (β : ℝ) (k : ℕ) :
    β + ((k + 2 : ℕ) : ℝ) + 1 / 2 = (β + k + 1 / 2) + 2 := by
  push_cast
  ring

/-- Simultaneously increasing total degree and inner index by two has positive pairing. -/
theorem integralInner_y_sq_dunklXuDisk_up_pos {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    0 < integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (X 1 ^ 2 * dunklXuDisk β (n + k) k) (dunklXuDisk β (n + (k + 2)) (k + 2))) := by
  rw [integralInner_y_sq_dunklXuDisk_inner_add_two hβ]
  simp only [Polynomial.integralInner, Nat.add_sub_cancel, shifted_outerParameter]
  simpa only [Polynomial.integralInner] using mul_pos (integralInner_jacobi_double_raise_top_pos (outerParameter_pos hβ k) n)
    (integralInner_X_sq_jacobi_add_two_pos hβ k)

/-- Increasing the inner index while keeping the total degree gives a negative pairing. -/
theorem integralInner_y_sq_dunklXuDisk_same_degree_neg {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (X 1 ^ 2 * dunklXuDisk β (n + 2 + k) k) (dunklXuDisk β (n + (k + 2)) (k + 2))) < 0 := by
  rw [integralInner_y_sq_dunklXuDisk_inner_add_two hβ]
  simp only [Polynomial.integralInner, Nat.add_sub_cancel, shifted_outerParameter]
  simpa only [Polynomial.integralInner] using mul_neg_of_neg_of_pos
    (integralInner_jacobi_double_raise_middle_neg (outerParameter_pos hβ k) n)
    (integralInner_X_sq_jacobi_add_two_pos hβ k)

/-- Increasing the inner index and decreasing total degree by two has positive pairing. -/
theorem integralInner_y_sq_dunklXuDisk_down_pos {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    0 < integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (X 1 ^ 2 * dunklXuDisk β (n + 4 + k) k) (dunklXuDisk β (n + (k + 2)) (k + 2))) := by
  rw [integralInner_y_sq_dunklXuDisk_inner_add_two hβ]
  simp only [Polynomial.integralInner, Nat.add_sub_cancel, shifted_outerParameter]
  simpa only [Polynomial.integralInner] using mul_pos (integralInner_jacobi_double_raise_bottom_pos (outerParameter_pos hβ k) n)
    (integralInner_X_sq_jacobi_add_two_pos hβ k)

/-- No other total degrees occur at the maximal inner-index step. -/
theorem integralInner_y_sq_dunklXuDisk_inner_add_two_eq_zero {β : ℝ} (hβ : -1 < β)
    (n m k : ℕ) (h₀ : n ≠ m) (h₂ : n - 2 ≠ m) (h₄ : n - 4 ≠ m) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (X 1 ^ 2 * dunklXuDisk β (n + k) k) (dunklXuDisk β (m + (k + 2)) (k + 2))) = 0 := by
  rw [integralInner_y_sq_dunklXuDisk_inner_add_two hβ]
  simp only [Polynomial.integralInner, Nat.add_sub_cancel, shifted_outerParameter]
  have he := integralInner_jacobi_double_raise (outerParameter_pos hβ k) n m
  simp only [Polynomial.integralInner] at he
  rw [he]
  simp [h₀, h₂, h₄]

end MvPolynomial
