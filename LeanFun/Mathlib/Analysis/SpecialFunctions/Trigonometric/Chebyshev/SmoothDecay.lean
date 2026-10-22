/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.MeasureTheory.Integral.IntegrableDerivative

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Integration by parts for Chebyshev coefficients

A first step towards finite-smoothness estimates. Reference: ATAP, Chapter 7.
-/

public section

namespace Polynomial.Chebyshev

open Real MeasureTheory intervalIntegral Set

/-- Integration by parts for the cosine pullback of a function (ATAP, Chapter 7).
The derivative is supplied explicitly to allow subsequent almost-everywhere APIs. -/
theorem coefficient_eq_integral_sin {f g' : ℝ → ℝ}
    (hf : ContinuousOn (fun θ ↦ f (cos θ)) (Icc 0 π))
    (hd : ∀ θ ∈ Ioo 0 π, HasDerivAt (fun θ ↦ f (cos θ)) (g' θ) θ)
    (hg : IntervalIntegrable g' volume 0 π) {n : ℕ} (hn : n ≠ 0) :
    (coefficient (n := n) ⟨f, by
      apply integrable_classicalMeasureT_mul_T ⟨_, ?_⟩ n
      apply integrable_classicalMeasureT_of_continuous_cos
      exact hf⟩) = -(2 / (π * n)) * ∫ θ in 0..π, g' θ * sin (n * θ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hb := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := π)
    (u := fun θ ↦ f (cos θ)) (v := fun θ ↦ sin (n * θ))
    (u' := g') (v' := fun θ ↦ (n : ℝ) * cos (n * θ))
    (by simpa only [uIcc_of_le pi_pos.le] using hf)
    (by fun_prop)
    (by simpa only [min_eq_left pi_pos.le, max_eq_right pi_pos.le] using hd)
    (fun θ _ ↦ by
      simpa only [Function.comp_def, mul_one, mul_comm] using
        (hasDerivAt_sin ((n : ℝ) * θ)).comp θ
          ((hasDerivAt_id θ).const_mul (n : ℝ)))
    hg (by apply Continuous.intervalIntegrable; fun_prop)
  simp only [mul_zero, sin_zero, mul_zero, sin_nat_mul_pi, sub_zero, zero_sub] at hb
  have hi : (n : ℝ) * (∫ θ in 0..π, f (cos θ) * cos (n * θ)) =
      -(∫ θ in 0..π, g' θ * sin (n * θ)) := by
    rw [← intervalIntegral.integral_const_mul]
    convert hb using 1
    congr 1
    funext θ
    ring
  rw [coefficient_eq_integral_cos, ite_eq_right hn]
  apply (mul_left_cancel₀ hn')
  calc
    _ = (2 / π) * ((n : ℝ) * ∫ θ in 0..π, f (cos θ) * cos (n * θ)) := by ring
    _ = _ := by rw [hi]; field_simp

/-- An integrable derivative of the cosine pullback bounds positive coefficients
by its L¹ norm divided by the index (ATAP, Chapter 7, integration-by-parts step). -/
theorem abs_coefficient_le_integral_abs_deriv {f g' : ℝ → ℝ}
    (hf : ContinuousOn (fun θ ↦ f (cos θ)) (Icc 0 π))
    (hd : ∀ θ ∈ Ioo 0 π, HasDerivAt (fun θ ↦ f (cos θ)) (g' θ) θ)
    (hg : IntervalIntegrable g' volume 0 π) {n : ℕ} (hn : n ≠ 0) :
    |(coefficient (n := n) ⟨f, by
      apply integrable_classicalMeasureT_mul_T ⟨_, ?_⟩ n
      apply integrable_classicalMeasureT_of_continuous_cos
      exact hf⟩)| ≤ (2 / (π * n)) * ∫ θ in 0..π, |g' θ| := by
  rw [coefficient_eq_integral_sin hf hd hg hn, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 2 / (π * (n : ℝ)))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∫ θ in 0..π, |g' θ * sin (n * θ)| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
        (f := fun θ ↦ g' θ * sin (n * θ)) pi_pos.le
    _ ≤ ∫ θ in 0..π, |g' θ| := by
      apply integral_mono_on pi_pos.le
        ((hg.mul_continuousOn (by fun_prop)).abs) hg.abs
      intro θ hθ
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)


/-- Integration by parts with a certified a.e. derivative representative (ATAP Chapter 7). -/
theorem coefficient_eq_integral_sin_of_absolutelyContinuous {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval (fun θ ↦ f (cos θ)) 0 π)
    (g : IntegrableDerivative (fun θ ↦ f (cos θ)) (volume.restrict (uIcc 0 π)))
    {n : ℕ} (hn : n ≠ 0) :
    (coefficient (n := n) ⟨f, by
      apply integrable_classicalMeasureT_mul_T ⟨_, ?_⟩ n
      apply integrable_classicalMeasureT_of_continuous_cos
      simpa only [uIcc_of_le pi_pos.le] using hf.continuousOn⟩) = -(2 / (π * n)) *
      ∫ θ in 0..π, g θ * sin (n * θ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : AbsolutelyContinuousOnInterval (fun θ : ℝ ↦ sin (n * θ)) 0 π :=
    (show ContDiff ℝ 1 (fun θ : ℝ ↦ sin (n * θ)) by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  let k : IntegrableDerivative (fun θ : ℝ ↦ sin (n * θ))
      (volume.restrict (uIcc 0 π)) := ⟨⟨fun θ ↦ (n : ℝ) * cos (n * θ),
        (intervalIntegrable_iff').mp (by apply Continuous.intervalIntegrable; fun_prop)⟩, by
      filter_upwards with θ
      simpa only [Function.comp_def, mul_one, mul_comm] using
        (hasDerivAt_sin ((n : ℝ) * θ)).comp θ
          ((hasDerivAt_id θ).const_mul (n : ℝ))⟩
  have hi := g.integral_mul_eq_sub k hf hs
  change (∫ θ in 0..π, f (cos θ) * ((n : ℝ) * cos (n * θ))) = _ at hi
  simp only [sin_nat_mul_pi, mul_zero, sin_zero, sub_zero, zero_sub] at hi
  have he : (n : ℝ) * (∫ θ in 0..π, f (cos θ) * cos (n * θ)) =
      -(∫ θ in 0..π, g θ * sin (n * θ)) := by
    rw [← intervalIntegral.integral_const_mul]
    convert hi using 1
    congr 1
    funext θ
    ring
  rw [coefficient_eq_integral_cos, ite_eq_right hn]
  apply (mul_left_cancel₀ hn')
  calc
    _ = (2 / π) * ((n : ℝ) * ∫ θ in 0..π, f (cos θ) * cos (n * θ)) := by ring
    _ = _ := by rw [he]; field_simp
end Polynomial.Chebyshev
