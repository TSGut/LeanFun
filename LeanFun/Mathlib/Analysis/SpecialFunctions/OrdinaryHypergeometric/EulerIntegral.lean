/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.Binomial
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.EulerMoments
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Euler's integral for the Gauss hypergeometric function

DLMF 15.6.1 in ordinary normalization, on the open unit disk. The complex
parameters satisfy `0 < re b` and `0 < re (c-b)`. No analytic continuation
outside the defining series disk is asserted here.
-/

public section
open MeasureTheory Set Polynomial Filter
namespace Complex

/-- Integrating the binomial series against any integrable weight on `[0,1]`.
This is the dominated-convergence step in Euler's integral, DLMF 15.6.1. -/
theorem hasSum_integral_binomial (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    {w : ℝ → ℂ} (hw : IntervalIntegrable w volume 0 1) :
    HasSum (fun n : ℕ ↦ ∫ t : ℝ in 0..1,
      w t * (((n.factorial : ℂ)⁻¹*(ascPochhammer ℂ n).eval a) * (z*(t : ℂ))^n))
      (∫ t : ℝ in 0..1, w t / (1-z*(t : ℂ))^a) := by
  let d : ℕ → ℂ := fun n ↦ (n.factorial : ℂ)⁻¹*(ascPochhammer ℂ n).eval a
  have hs : Summable (fun n ↦ ‖d n * z^n‖) := summable_norm_pochhammer_mul_pow a hz
  have hi (n : ℕ) : IntervalIntegrable
      (fun t ↦ w t * (d n * (z*(t : ℂ))^n)) volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n t ↦ ‖w t‖ * ‖d n * z^n‖)
    (fun n ↦ by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (hi n).1.aestronglyMeasurable) ?_ ?_ ?_ ?_
  · intro n
    filter_upwards with t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by simpa [abs_of_pos ht'.1] using ht'.2
    calc
      ‖w t * (d n * (z*(t : ℂ))^n)‖ =
          ‖w t‖ * (‖d n * z^n‖ * ‖(t : ℂ)‖^n) := by
        simp only [mul_pow, norm_mul, norm_pow]; ring
      _ ≤ ‖w t‖ * ‖d n * z^n‖ := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ht1))
          (norm_nonneg _)
  · exact Eventually.of_forall fun t _ ↦ hs.mul_left ‖w t‖
  · simpa only [tsum_mul_left] using hw.norm.mul_const (∑' n, ‖d n * z^n‖)
  · filter_upwards with t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
    have hzt : ‖z*(t : ℂ)‖ < 1 := by
      rw [norm_mul]
      have ht1 : ‖(t : ℂ)‖ ≤ 1 := by simpa [abs_of_pos ht'.1] using ht'.2
      exact (mul_le_of_le_one_right (norm_nonneg z) ht1).trans_lt hz
    simpa only [div_eq_mul_inv, one_mul, d] using
      (hasSum_pochhammer_mul_pow a hzt).mul_left (w t)


end Complex
