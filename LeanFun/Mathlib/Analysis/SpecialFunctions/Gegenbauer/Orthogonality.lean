/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Orthogonality
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Jacobi

import Mathlib.Tactic.Linarith

/-! # Gegenbauer orthogonality
Transfer Jacobi orthogonality through the algebraic bridge. The basic Gegenbauer
definition remains independent of Jacobi analysis. The range includes negative
parameters greater than -1/2. Reference: DLMF Table 18.3.1 and 18.7.1.
-/

public section
open MeasureTheory Real
namespace Polynomial

/-- The divided bridge in the orthogonality range (DLMF 18.7.1).
It includes parameter zero, where positive-degree Gegenbauer polynomials vanish. -/
theorem gegenbauer_eq_jacobi_mul {lam : ℝ} (hlam : -(1 / 2) < lam) (n : ℕ) :
    gegenbauer lam n =
      C ((ascPochhammer ℝ n).eval (2 * lam) /
        (ascPochhammer ℝ n).eval (lam + 1 / 2)) *
          jacobi (lam - 1 / 2) (lam - 1 / 2) n := by
  have hd : (ascPochhammer ℝ n).eval (lam + 1 / 2) ≠ 0 :=
    (ascPochhammer_pos n _ (by linarith)).ne'
  have h := gegenbauer_jacobi lam n
  norm_num only [map_div₀, map_one, map_ofNat] at h
  apply mul_left_cancel₀ (C_ne_zero.mpr hd)
  rw [h, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hd]

/-- The bridge factor is nonzero for nonzero admissible parameters (DLMF 18.7.1). -/
theorem gegenbauer_jacobi_factor_ne_zero {lam : ℝ} (hlam : -(1 / 2) < lam)
    (hzero : lam ≠ 0) (n : ℕ) :
    (ascPochhammer ℝ n).eval (2 * lam) /
      (ascPochhammer ℝ n).eval (lam + 1 / 2) ≠ 0 := by
  apply div_ne_zero _ (ascPochhammer_pos n _ (by linarith)).ne'
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    apply mul_ne_zero ih
    rcases n with _ | n
    · simpa using (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hzero)
    · have : 0 < 2 * lam + (n + 1 : ℕ) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) n]
      exact this.ne'

/-- Exact degree throughout the nondegenerate orthogonality range (DLMF Table 18.3.1). -/
theorem degree_gegenbauer_of_neg_half_lt {lam : ℝ} (hlam : -(1 / 2) < lam)
    (hzero : lam ≠ 0) (n : ℕ) : (gegenbauer lam n).degree = n := by
  rw [gegenbauer_eq_jacobi_mul hlam, degree_C_mul (gegenbauer_jacobi_factor_ne_zero hlam hzero n)]
  exact degree_jacobi_of_neg_one_lt (by linarith) (by linarith) n

/-- The Gegenbauer polynomial sequence (DLMF Table 18.3.1). -/
@[expose] noncomputable def gegenbauerSequence {lam : ℝ} (hlam : -(1 / 2) < lam)
    (hzero : lam ≠ 0) : Sequence ℝ where
  elems' := gegenbauer lam
  degree_eq' := degree_gegenbauer_of_neg_half_lt hlam hzero

/-- The sequence uses the independent Gegenbauer definition (DLMF Table 18.3.1). -/
@[simp] theorem gegenbauerSequence_apply {lam : ℝ} (hlam : -(1 / 2) < lam)
    (hzero : lam ≠ 0) (n : ℕ) : gegenbauerSequence hlam hzero n = gegenbauer lam n := rfl

/-- Pairwise Gegenbauer orthogonality, also valid at the degenerate parameter zero
(DLMF Table 18.3.1). -/
theorem integral_mul_gegenbauer_eq_zero {lam : ℝ} (hlam : -(1 / 2) < lam)
    {m n : ℕ} (hmn : m ≠ n) :
    ∫ x, (gegenbauer lam m).eval x * (gegenbauer lam n).eval x ∂gegenbauerMeasure lam = 0 := by
  rw [gegenbauerMeasure_eq_jacobiMeasure]
  simp_rw [gegenbauer_eq_jacobi_mul hlam, eval_mul, eval_C]
  simp_rw [mul_mul_mul_comm]
  rw [integral_const_mul, integral_mul_jacobi_eq_zero (by linarith) (by linarith) hmn, mul_zero]

/-- Gegenbauer polynomials satisfy the general orthogonality predicate (DLMF Table 18.3.1). -/
theorem isOrthogonal_gegenbauerSequence {lam : ℝ} (hlam : -(1 / 2) < lam)
    (hzero : lam ≠ 0) : (gegenbauerSequence hlam hzero).IsOrthogonal (gegenbauerMeasure lam) where
  integrable _ _ := (hasFiniteMoments_gegenbauerMeasure hlam).integrable_mul _ _
  orthogonal _ _ hmn := integral_mul_gegenbauer_eq_zero hlam hmn

end Polynomial
