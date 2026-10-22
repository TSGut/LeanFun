/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.SymmetricDoubleConnection

/-! # Pairing signs for double symmetric Jacobi raising
The algebraic connection coefficients give actual weighted integral signs.
Reference: DLMF 18.9 and Table 18.3.1.
-/

public section
namespace Polynomial

private theorem integralInner_jacobi_diagonal {β : ℝ} (hβ : -1 < β) (n m : ℕ) :
    integralInner (jacobiMeasure β β) (IntegrablePair.of (jacobiMeasure β β) (jacobi β β n) (jacobi β β m)) =
      if n = m then integralInner (jacobiMeasure β β) (IntegrablePair.of (jacobiMeasure β β) (jacobi β β m) (jacobi β β m)) else 0 := by
  by_cases h : n = m
  · simp [h]
  · rw [ite_eq_right h]
    exact integral_mul_jacobi_eq_zero hβ hβ h

private theorem integralInner_jacobi_self_pos {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    0 < integralInner (jacobiMeasure β β) (IntegrablePair.of (jacobiMeasure β β) (jacobi β β n) (jacobi β β n)) := by
  simpa [integralInner_self] using
    hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ _ ((jacobiSequence hβ hβ).ne_zero n)

/-- Exact three-term support of the shifted-weight pairing. -/
theorem integralInner_jacobi_double_raise {β : ℝ} (hβ : -1 < β) (n m : ℕ) :
    integralInner (jacobiMeasure (β + 2) (β + 2)) (IntegrablePair.of (jacobiMeasure (β + 2) (β + 2)) (jacobi β β n) (jacobi (β + 2) (β + 2) m) (h := (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith)).integrable_mul _ _)) =
      (jacobiSymmetricDoubleRaiseA β n * (if n = m then 1 else 0) +
       jacobiSymmetricDoubleRaiseB β n * (if n - 2 = m then 1 else 0) +
       jacobiSymmetricDoubleRaiseC β n * (if n - 4 = m then 1 else 0)) *
        integralInner (jacobiMeasure (β + 2) (β + 2)) (IntegrablePair.of (jacobiMeasure (β + 2) (β + 2)) (jacobi (β + 2) (β + 2) m) (jacobi (β + 2) (β + 2) m) (h := (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith)).integrable_mul _ _)) := by
  have hb : -1 < β + 2 := by linarith
  have hM := hasFiniteMoments_jacobiMeasure hb hb
  have he := congrArg (fun p : ℝ[X] => integralInner (jacobiMeasure (β+2) (β+2))
    (hM.pair p (jacobi (β+2) (β+2) m))) (jacobi_symmetric_double_raise hβ n)
  rw [he]
  simp only [integralInner_add_left (hasFiniteMoments_jacobiMeasure hb hb),
    integralInner_smul_left (h := hM.integrable_mul _ _)]
  rw [integralInner_jacobi_diagonal hb n m, integralInner_jacobi_diagonal hb (n - 2) m,
    integralInner_jacobi_diagonal hb (n - 4) m]
  split_ifs <;> ring

/-- Equal-degree shifted-weight pairings are strictly positive, including degrees zero and one. -/
theorem integralInner_jacobi_double_raise_top_pos {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    0 < integralInner (jacobiMeasure (β + 2) (β + 2)) (IntegrablePair.of (jacobiMeasure (β + 2) (β + 2)) (jacobi β β n) (jacobi (β + 2) (β + 2) n) (h := (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith)).integrable_mul _ _)) := by
  rw [integralInner_jacobi_double_raise hβ]
  have hb : jacobiSymmetricDoubleRaiseB β n * (if n - 2 = n then 1 else 0) = 0 := by
    by_cases hn : n < 2
    · rw [jacobiSymmetricDoubleRaiseB_eq_zero hn, zero_mul]
    · rw [ite_eq_right (by omega), mul_zero]
  have hc : jacobiSymmetricDoubleRaiseC β n * (if n - 4 = n then 1 else 0) = 0 := by
    by_cases hn : n < 4
    · rw [jacobiSymmetricDoubleRaiseC_eq_zero hn, zero_mul]
    · rw [ite_eq_right (by omega), mul_zero]
  simp only [ite_true, mul_one, hb, hc, add_zero]
  exact mul_pos (jacobiSymmetricDoubleRaiseA_pos hβ n) (integralInner_jacobi_self_pos (by linarith) n)

/-- Dropping two degrees gives a strictly negative pairing. -/
theorem integralInner_jacobi_double_raise_middle_neg {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    integralInner (jacobiMeasure (β + 2) (β + 2)) (IntegrablePair.of (jacobiMeasure (β + 2) (β + 2)) (jacobi β β (n + 2)) (jacobi (β + 2) (β + 2) n) (h := (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith)).integrable_mul _ _)) < 0 := by
  rw [integralInner_jacobi_double_raise hβ]
  have hc : jacobiSymmetricDoubleRaiseC β (n + 2) *
      (if n + 2 - 4 = n then 1 else 0) = 0 := by
    by_cases hn : n + 2 < 4
    · rw [jacobiSymmetricDoubleRaiseC_eq_zero hn, zero_mul]
    · rw [ite_eq_right (by omega), mul_zero]
  rw [ite_eq_right (by omega : n + 2 ≠ n)]
  simp only [mul_zero, zero_add, Nat.add_sub_cancel, ite_true, mul_one, hc, add_zero]
  exact mul_neg_of_neg_of_pos (jacobiSymmetricDoubleRaiseB_neg hβ n)
    (integralInner_jacobi_self_pos (by linarith) n)

/-- Dropping four degrees gives a strictly positive pairing. -/
theorem integralInner_jacobi_double_raise_bottom_pos {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    0 < integralInner (jacobiMeasure (β + 2) (β + 2)) (IntegrablePair.of (jacobiMeasure (β + 2) (β + 2)) (jacobi β β (n + 4)) (jacobi (β + 2) (β + 2) n) (h := (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith)).integrable_mul _ _)) := by
  rw [integralInner_jacobi_double_raise hβ, ite_eq_right (by omega : n + 4 ≠ n),
    ite_eq_right (by omega : n + 4 - 2 ≠ n)]
  simp only [mul_zero, zero_add, Nat.add_sub_cancel, ite_true, mul_one]
  exact mul_pos (jacobiSymmetricDoubleRaiseC_pos hβ n)
    (integralInner_jacobi_self_pos (by linarith) n)

end Polynomial
