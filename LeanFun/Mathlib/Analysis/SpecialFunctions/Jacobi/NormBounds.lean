/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Norm
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.PolynomialBounds
import Mathlib.Tactic.GCongr

/-!
# Polynomial bounds for reciprocal Jacobi norms

Integer comparisons for Gamma give polynomial upper bounds for reciprocal
squared norms throughout alpha,beta > -1. The exponents are nonsharp.
Reference: DLMF Table 18.3.1 and Gamma monotonicity on [2,infinity).
-/

public section
namespace Polynomial
open Real MeasureTheory

/-- Jacobi squared norms are positive throughout the orthogonality range. -/
theorem integral_sq_jacobi_pos {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    0 < ∫ x, (jacobi α β n).eval x ^ 2 ∂jacobiMeasure α β := by
  simpa only [jacobiSequence_apply] using
    hasPositiveDefiniteIntegral_jacobiMeasure hα hβ _ ((jacobiSequence hα hβ).ne_zero n)

/-- A factorial comparison bound on reciprocal norms, away from the first
three degrees. The small degrees are handled separately in the global bound. -/
theorem inv_integral_sq_jacobi_succ_le {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n k : ℕ) (hn : 2 ≤ n) (hk : α + β + 1 ≤ k) :
    (∫ x, (jacobi α β (n + 1)).eval x ^ 2 ∂jacobiMeasure α β)⁻¹ ≤
      ((2 * (n : ℝ) + α + β + 3) * (n + 1) * ((n : ℝ) + k) ^ k) /
        (2 : ℝ) ^ (α + β + 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hA := factorial_le_Gamma_nat_add (show 1 ≤ n by omega)
    (show 1 ≤ α + 2 by linarith)
  have hB := factorial_le_Gamma_nat_add (show 1 ≤ n by omega)
    (show 1 ≤ β + 2 by linarith)
  have hD := Gamma_nat_add_le_factorial_mul_pow n k
    (show α + β + 2 ≤ k + 1 by linarith) (by linarith : 2 ≤ (n : ℝ) + (α + β + 2))
  simp only [GammaOn, GammaPoint.ofPos] at hA hB hD
  have hAg : 0 < Gamma ((n : ℝ) + α + 2) := Gamma_pos_of_pos (by linarith)
  have hBg : 0 < Gamma ((n : ℝ) + β + 2) := Gamma_pos_of_pos (by linarith)
  have hR : 0 < (2 : ℝ) ^ (α + β + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hd : 0 ≤ 2 * (n : ℝ) + α + β + 3 := by linarith
  have hF : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  have hprod : Gamma ((n : ℝ) + α + β + 2) * n.factorial ≤
      ((n : ℝ) + k) ^ k * (Gamma ((n : ℝ) + α + 2) * Gamma ((n : ℝ) + β + 2)) := by
    calc
      _ ≤ ((n.factorial : ℝ) * ((n : ℝ) + k) ^ k) * n.factorial := by
        apply mul_le_mul_of_nonneg_right _ hF
        simpa only [add_assoc] using hD
      _ = ((n : ℝ) + k) ^ k * ((n.factorial : ℝ) * n.factorial) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul _ _ hF hAg.le
        · simpa only [add_assoc] using hA
        · simpa only [add_assoc] using hB
  rw [integral_sq_jacobi_succ hα hβ, inv_div, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [GammaOn, GammaPoint.ofPos]
  apply (div_le_div_iff₀ (mul_pos (mul_pos hR hAg) hBg) hR).mpr
  convert mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (mul_nonneg hd (show 0 ≤ (n : ℝ) + 1 by positivity)) hR.le) using 1 <;> ring

/-- An explicit fixed-power bound for reciprocal norms in degrees at least three. -/
theorem inv_integral_sq_jacobi_succ_le_polynomial {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n k : ℕ) (hn : 2 ≤ n)
    (hk : α + β + 1 ≤ k) :
    (∫ x, (jacobi α β (n + 1)).eval x ^ 2 ∂jacobiMeasure α β)⁻¹ ≤
      ((2 + |α + β + 3|) * ((k : ℝ) + 1) ^ k / (2 : ℝ) ^ (α + β + 1)) *
        ((n : ℝ) + 1) ^ (k + 2) := by
  apply (inv_integral_sq_jacobi_succ_le hα hβ n k hn hk).trans
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hd : 0 ≤ 2 * (n : ℝ) + α + β + 3 := by linarith
  calc
    _ ≤ (((2 + |α + β + 3|) * ((n : ℝ) + 1)) * (n + 1) *
        (((k : ℝ) + 1) * (n + 1)) ^ k) / (2 : ℝ) ^ (α + β + 1) := by
      gcongr
      · nlinarith [le_abs_self (α + β + 3), mul_nonneg hn0 (abs_nonneg (α + β + 3))]
      · nlinarith [Nat.cast_nonneg (α := ℝ) k]
    _ = _ := by rw [mul_pow, pow_add, pow_two]; ring

/-- A global reciprocal-norm bound, including the first three degrees explicitly. -/
@[expose] noncomputable def jacobiReciprocalNormBound (α β : Set.Ioi (-1 : ℝ)) (k : ℕ) : ℝ :=
  1 + (∫ x, (jacobi α.val β.val 0).eval x ^ 2 ∂jacobiMeasure α.val β.val)⁻¹ +
    (∫ x, (jacobi α.val β.val 1).eval x ^ 2 ∂jacobiMeasure α.val β.val)⁻¹ +
    (∫ x, (jacobi α.val β.val 2).eval x ^ 2 ∂jacobiMeasure α.val β.val)⁻¹ +
    (2 + |α.val + β.val + 3|) * ((k : ℝ) + 1) ^ k / (2 : ℝ) ^ (α.val + β.val + 1)

/-- The global reciprocal-norm constant is positive for every integrable Jacobi weight. -/
theorem jacobiReciprocalNormBound_pos {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (k : ℕ) :
    0 < jacobiReciprocalNormBound ⟨α, hα⟩ ⟨β, hβ⟩ k := by
  have h0 := integral_sq_jacobi_pos hα hβ 0
  have h1 := integral_sq_jacobi_pos hα hβ 1
  have h2 := integral_sq_jacobi_pos hα hβ 2
  unfold jacobiReciprocalNormBound
  positivity

/-- Reciprocal squared norms have a global polynomial bound, including degree zero. -/
theorem inv_integral_sq_jacobi_le_polynomial {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (k : ℕ) (hk : α + β + 1 ≤ k) (n : ℕ) :
    (∫ x, (jacobi α β n).eval x ^ 2 ∂jacobiMeasure α β)⁻¹ ≤
      jacobiReciprocalNormBound ⟨α, hα⟩ ⟨β, hβ⟩ k * ((n : ℝ) + 1) ^ (k + 2) := by
  let B : ℝ := (2 + |α + β + 3|) * ((k : ℝ) + 1) ^ k / (2 : ℝ) ^ (α + β + 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h0 := inv_nonneg.mpr (integral_sq_jacobi_pos hα hβ 0).le
  have h1 := inv_nonneg.mpr (integral_sq_jacobi_pos hα hβ 1).le
  have h2 := inv_nonneg.mpr (integral_sq_jacobi_pos hα hβ 2).le
  have hC := (jacobiReciprocalNormBound_pos hα hβ k).le
  have hBC : B ≤ jacobiReciprocalNormBound ⟨α, hα⟩ ⟨β, hβ⟩ k := by
    change B ≤ 1 + _ + _ + _ + B
    linarith
  have hsmall (j : ℕ) (hj : j ≤ 2) :
      (∫ x, (jacobi α β j).eval x ^ 2 ∂jacobiMeasure α β)⁻¹ ≤
        jacobiReciprocalNormBound ⟨α, hα⟩ ⟨β, hβ⟩ k := by
    unfold jacobiReciprocalNormBound
    change _ ≤ 1 + _ + _ + _ + B
    interval_cases j <;> linarith
  by_cases hn : n ≤ 2
  · apply (hsmall n hn).trans
    exact le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hm : 2 ≤ m := by omega
  apply (inv_integral_sq_jacobi_succ_le_polynomial hα hβ m k hm hk).trans
  change B * ((m : ℝ) + 1) ^ (k + 2) ≤ _
  apply mul_le_mul hBC _ (by positivity) hC
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  linarith

end Polynomial
