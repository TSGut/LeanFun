/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.SymmetricConnection
import Mathlib.Tactic.Positivity

/-! # Signs of the symmetric Jacobi connection coefficients
The signs are strict in the full orthogonality range; only the absent lower
degrees have zero coefficients. Reference: DLMF 18.9.
-/

public section
namespace Polynomial

/-- The unchanged-degree raising coefficient is strictly positive. -/
theorem jacobiSymmetricRaiseA_pos {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    0 < jacobiSymmetricRaiseA β n := by
  rcases n with _ | _ | n
  · norm_num [jacobiSymmetricRaiseA]
  · exact div_pos (by linarith) (by linarith)
  · have hn := Nat.cast_nonneg (α := ℝ) n
    have h₀ : 0 < 2 * (n : ℝ) + 2 * β + 5 := by linarith
    have h₁ : 0 < 2 * (n : ℝ) + 2 * β + 6 := by linarith
    have h₂ : 0 < 2 * (n : ℝ) + 2 * β + 4 := by linarith
    have h₃ : 0 < (n : ℝ) + 2 * β + 3 := by linarith
    have h₄ : 0 < (n : ℝ) + 2 * β + 4 := by linarith
    dsimp [jacobiSymmetricRaiseA]
    positivity

/-- In degrees at least two, the lower raising coefficient is strictly negative. -/
theorem jacobiSymmetricRaiseB_neg {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    jacobiSymmetricRaiseB β (n + 2) < 0 := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  have h₀ : 0 < 2 * (n : ℝ) + 2 * β + 5 := by linarith
  have h₁ : 0 < 2 * (n : ℝ) + 2 * β + 6 := by linarith
  have h₂ : 0 < 2 * (n : ℝ) + 2 * β + 4 := by linarith
  have h₃ : 0 < (n : ℝ) + β + 2 := by linarith
  dsimp [jacobiSymmetricRaiseB]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr (mul_pos (mul_pos h₀ h₁) h₂))
    (neg_neg_of_pos (mul_pos h₁ (sq_pos_of_pos h₃)))

/-- The lower raising coefficient is nonpositive, including the initial degrees. -/
theorem jacobiSymmetricRaiseB_nonpos {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    jacobiSymmetricRaiseB β n ≤ 0 := by
  rcases n with _ | _ | n
  · exact le_rfl
  · exact le_rfl
  · exact (jacobiSymmetricRaiseB_neg hβ n).le

/-- The degree-plus-two boundary-weight coefficient is strictly negative. -/
theorem jacobiSymmetricLowerA_neg {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    jacobiSymmetricLowerA β n < 0 := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  have h₀ : 0 < 2 * (n : ℝ) + 2 * β + 2 := by linarith
  have h₁ : 0 < (n : ℝ) + 2 * β + 2 := by linarith
  have h₂ : 0 < 2 * (n : ℝ) + 2 * β + 3 := by linarith
  have h₃ : 0 < 2 * (n : ℝ) + 2 * β + 4 := by linarith
  dsimp [jacobiSymmetricLowerA]
  apply mul_neg_of_pos_of_neg (by positivity)
  apply mul_neg_of_neg_of_pos _ h₀
  apply mul_neg_of_neg_of_pos _ h₁
  apply mul_neg_of_neg_of_pos _ (by positivity)
  exact mul_neg_of_neg_of_pos (by norm_num) (by positivity)

/-- The unchanged-degree boundary-weight coefficient is strictly positive. -/
theorem jacobiSymmetricLowerB_pos {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    0 < jacobiSymmetricLowerB β n := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  have h₀ : 0 < 2 * (n : ℝ) + 2 * β + 2 := by linarith
  have h₁ : 0 < (n : ℝ) + 2 * β + 2 := by linarith
  have h₂ : 0 < 2 * (n : ℝ) + 2 * β + 3 := by linarith
  have h₃ : 0 < 2 * (n : ℝ) + 2 * β + 4 := by linarith
  have h₄ : 0 < (n : ℝ) + β + 1 := by linarith
  dsimp [jacobiSymmetricLowerB]
  positivity

end Polynomial
