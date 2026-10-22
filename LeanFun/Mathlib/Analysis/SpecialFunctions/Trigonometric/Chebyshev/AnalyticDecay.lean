/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexCoefficients
public import LeanFun.Mathlib.Analysis.Complex.BernsteinEllipseDecay

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Analytic Chebyshev coefficient decay

Reference: ATAP, Theorem 8.1. The ellipse is open; no continuity on its
boundary is assumed.
-/

public section

open Complex Real MeasureTheory Set

namespace Polynomial.Chebyshev

/-- Analytic ellipse data restrict to continuous interval data (ATAP 8.1). -/
theorem continuousOn_real_of_analytic {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 1 < ρ) (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ⟨ρ, hρ⟩)) :
    ContinuousOn (fun x : ℝ ↦ f x) (Icc (-1) 1) :=
  hf.continuousOn.comp Complex.continuous_ofReal.continuousOn
    (fun _x hx ↦ ofReal_mem_bernsteinEllipse hρ hx)

private theorem integral_cos_pullback {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1)) (n : ℕ) :
    (∫ θ in 0..2 * π, f (Real.cos θ) *
      ((Real.cos (n * θ) : ℂ) - (Real.sin (n * θ) : ℂ) * I)) =
      2 * ∫ θ in 0..π, f (Real.cos θ) * (Real.cos (n * θ) : ℂ) := by
  let g (θ : ℝ) := f (Real.cos θ) *
    ((Real.cos (n * θ) : ℂ) - (Real.sin (n * θ) : ℂ) * I)
  have hc : Continuous (fun θ ↦ f (Real.cos θ)) :=
    hf.comp_continuous continuous_cos (fun θ ↦ ⟨neg_one_le_cos θ, cos_le_one θ⟩)
  have hg : Continuous g := hc.mul (by fun_prop)
  have he (θ : ℝ) : g θ + g (2 * π - θ) =
      2 * (f (Real.cos θ) * (Real.cos (n * θ) : ℂ)) := by
    dsimp [g]
    rw [Real.cos_two_pi_sub, mul_sub (n : ℝ), Real.cos_nat_mul_two_pi_sub,
      Real.sin_nat_mul_two_pi_sub, Complex.ofReal_neg]
    ring
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (a := 0) (b := π))
    (hg.intervalIntegrable (a := π) (b := 2 * π))
  have ht := intervalIntegral.integral_comp_sub_left g (2 * π) (a := 0) (b := π)
  have hp : 2 * π - π = π := by ring
  rw [hp, sub_zero] at ht
  change (∫ θ in 0..2 * π, g θ) = _
  have hgi : IntervalIntegrable (fun θ ↦ g (2 * π - θ)) volume 0 π :=
    (hg.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 π
  rw [← hs, ← ht, ← intervalIntegral.integral_add (hg.intervalIntegrable 0 π) hgi]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]

/-- Unit-circle contour representation of complex Chebyshev coefficients
(ATAP, Theorems 3.1 and 8.1). -/
theorem complexCoefficient_eq_laurent_integral {f : ℂ → ℂ}
    (hf : ContinuousOn (fun x : ℝ ↦ f x) (Icc (-1) 1)) (n : ℕ) :
    (complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun x : ℝ ↦ f x) hf n)) =
      (if n = 0 then 1 else 2 : ℂ) * (2 * π * I : ℂ)⁻¹ *
        circleIntegralOn (joukowskiLaurentInput ⟨fun x => f x, hf.domRestrict⟩ n) := by
  have hz (θ : ℝ) : circleMap 0 1 θ ≠ 0 := by simp [circleMap_zero]
  have he (θ : ℝ) : (circleMap 0 1 θ * I) *
      (f ((circleMap 0 1 θ).re : ℂ) / circleMap 0 1 θ ^ (n + 1)) =
      I * (f (Real.cos θ) * ((Real.cos (n * θ) : ℂ) -
        (Real.sin (n * θ) : ℂ) * I)) := by
    rw [circleMap_zero_re, one_mul]
    have hp : (circleMap 0 1 θ ^ n)⁻¹ =
        (Real.cos (n * θ) : ℂ) - (Real.sin (n * θ) : ℂ) * I := by
      rw [circleMap_zero_pow, one_pow, circleMap_zero_inv]
      simp only [inv_one, circleMap_zero, Complex.ofReal_one, one_mul, Complex.exp_mul_I]
      simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, sub_eq_add_neg, neg_mul]
    rw [← hp, pow_succ]
    field_simp
  rw [complexCoefficient_eq_integral_cos hf,
    (circleIntegralOn_spec (joukowskiLaurentInput ⟨fun x => f x, hf.domRestrict⟩ n)).2]
  change _ = (if n = 0 then 1 else 2 : ℂ) * (2 * π * I : ℂ)⁻¹ *
    (∫ θ in 0..2 * π, (circleMap 0 1 θ * I) *
      (f ((circleMap 0 1 θ).re : ℂ) / circleMap 0 1 θ ^ (n + 1)))
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, integral_cos_pullback hf]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  split_ifs <;> push_cast <;> field_simp

/-- Analyticity and boundedness in the open Bernstein ellipse imply geometric
Chebyshev coefficient decay, with the sharper constant at zero (ATAP, Theorem 8.1). -/
theorem norm_complexCoefficient_le_of_analytic {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ⟨ρ, hρ⟩))
    (hb : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖f z‖ ≤ M) (n : ℕ) :
    ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun x : ℝ ↦ f x) (continuousOn_real_of_analytic hρ hf) n))‖ ≤
      (if n = 0 then 1 else 2 : ℝ) * M / ρ ^ n := by
  have hc : ContinuousOn (fun x : ℝ ↦ f x) (Icc (-1) 1) :=
    hf.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun _x hx ↦ ofReal_mem_bernsteinEllipse hρ hx)
  rw [complexCoefficient_eq_laurent_integral hc, mul_assoc, norm_mul]
  have h := norm_joukowski_laurent_integral_le ⟨ρ, hρ⟩ hf hb n
    (joukowskiLaurentInput ⟨fun x => f x, hc.domRestrict⟩ n) (by
      intro z
      rw [joukowskiLaurentInput_apply, joukowski_unitCircle]
      rfl)
  split_ifs <;> simp only [norm_one, Complex.norm_ofNat, mul_div_assoc, one_mul] <;> linarith

end Polynomial.Chebyshev
