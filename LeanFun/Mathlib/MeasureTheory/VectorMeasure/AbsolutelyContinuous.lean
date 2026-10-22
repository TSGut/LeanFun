/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.MeasureTheory.Integral.IntegrableDerivative

public import LeanFun.Mathlib.MeasureTheory.VectorMeasure.IntegralWithDensity
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Stieltjes measures of absolutely continuous functions

Identifying the Stieltjes measure with its derivative density lets bounded-variation
integration by parts apply to Lebesgue integrals (ATAP, Chapter 7).
-/

public section

open Set MeasureTheory intervalIntegral

namespace BoundedVariationOn

/-- A continuous bounded-variation function whose increments are integrals of `g`
has Stieltjes measure with density `g`. -/
theorem vectorMeasure_eq_withDensityᵥ_of_integral_eq_sub {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hc : Continuous f) (hg : Integrable g)
    (hFTC : ∀ a b : ℝ, a ≤ b → ∫ x in a..b, g x = f b - f a) :
    hf.vectorMeasure = volume.withDensityᵥ g := by
  apply VectorMeasure.ext_of_Icc _ _
  intro a b hab
  rw [hf.vectorMeasure_Icc hab, hc.continuousAt.continuousWithinAt.rightLim_eq,
    hc.continuousAt.continuousWithinAt.leftLim_eq,
    withDensityᵥ_apply hg measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, hFTC a b hab]

/-- The Stieltjes measure of a globally bounded-variation, locally absolutely
continuous function is its derivative density. -/
theorem vectorMeasure_eq_withDensityᵥ_deriv {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hc : Continuous f)
    (ha : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (g : IntegrableDerivative f volume) :
    hf.vectorMeasure = volume.withDensityᵥ (g : ℝ → ℝ) := by
  apply hf.vectorMeasure_eq_withDensityᵥ_of_integral_eq_sub hc g.integrable
  intro a b _
  let d : IntegrableDerivative f (volume.restrict (uIcc a b)) :=
    ⟨⟨g, g.integrable.restrict⟩, ae_restrict_of_ae g.hasDerivAt⟩
  exact d.integral_eq_sub (ha a b)

/-- Integration by parts with a bounded-variation factor and an absolutely
continuous primitive, given by its integral increments. Jumps of `f` are allowed. -/
theorem integral_mul_eq_sub_vectorMeasure {f g g' : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (hc : Continuous g) (hd : Integrable g')
    (hFTC : ∀ a b : ℝ, a ≤ b → ∫ x in a..b, g' x = g b - g a)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, g' x * f x =
      g b * f.rightLim b - g a * f.leftLim a - ∫ᵛ x in Icc a b, g x ∂•hf.vectorMeasure := by
  have hleft : f.leftLim =ᵐ[volume] f := by
    filter_upwards [hf.countable_not_continuousAt.ae_notMem volume] with x hx
    exact (not_not.mp hx).continuousWithinAt.leftLim_eq
  have hbound : ∀ᵐ x ∂volume,
      ‖f.leftLim x‖ ≤ ‖f.leftLim 0‖ + (eVariationOn f.leftLim univ).toReal := by
    filter_upwards with x
    have hdist := hf.leftLim.dist_le (mem_univ (0 : ℝ)) (mem_univ x)
    calc ‖f.leftLim x‖
      _ ≤ ‖f.leftLim 0‖ + ‖f.leftLim x - f.leftLim 0‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖f.leftLim 0‖ + (eVariationOn f.leftLim univ).toReal := by
        gcongr
        simpa [dist_eq_norm_sub, norm_sub_rev] using hdist
  have hibp := hf.setIntegral_Icc_leftLim_vectorMeasure_eq_sub
    (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) hg hab
  rw [hg.vectorMeasure_eq_withDensityᵥ_of_integral_eq_sub hc hd hFTC,
    VectorMeasure.setIntegral_withDensityᵥ_of_bound hd
      hf.leftLim.stronglyMeasurable.aestronglyMeasurable hbound measurableSet_Icc] at hibp
  have hright : g.rightLim = g := funext fun x ↦
    hc.continuousAt.continuousWithinAt.rightLim_eq
  rw [hright, hc.continuousAt.continuousWithinAt.leftLim_eq] at hibp
  simp only [ContinuousLinearMap.flip_flip, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] at hibp
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  calc (∫ x in Icc a b, g' x * f x)
    _ = ∫ x in Icc a b, g' x * f.leftLim x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hleft.restrict] with x hx
      rw [hx]
    _ = _ := hibp

/-- A primitive vanishing at the endpoints bounds the integral by its supremum
norm times the total variation of the other factor. This allows jumps of `f`. -/
theorem abs_integral_mul_le_of_primitive {f g g' : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (hc : Continuous g) (hd : Integrable g')
    (hFTC : ∀ a b : ℝ, a ≤ b → ∫ x in a..b, g' x = g b - g a)
    {a b : ℝ} (hab : a ≤ b) (ha : g a = 0) (hb : g b = 0)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ Icc a b, |g x| ≤ C) :
    |∫ x in a..b, g' x * f x| ≤ C * (eVariationOn f univ).toReal := by
  rw [hf.integral_mul_eq_sub_vectorMeasure hg hc hd hFTC hab, ha, hb]
  simp only [zero_mul, sub_self, zero_sub, abs_neg]
  have hi := VectorMeasure.norm_setIntegral_le_of_norm_le_const
    (μ := hf.vectorMeasure) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (s := Icc a b) (f := g) hbound
  simp only [ContinuousLinearMap.opNorm_lsmul, mul_one, Real.norm_eq_abs] at hi
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply ENNReal.toReal_mono hf
  exact (measure_mono (subset_univ _)).trans hf.variation_vectorMeasure_univ_le

end BoundedVariationOn
