/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Coefficients
public import LeanFun.Mathlib.MeasureTheory.VectorMeasure.BoundedVariationInterval
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Chebyshev coefficients of functions of bounded variation

The bounded-variation base case of ATAP, Theorem 7.1, allowing jumps.
-/

public section

namespace Polynomial.Chebyshev

open Real Set MeasureTheory intervalIntegral
open scoped NNReal

/-- Bounded variation supplies classical coefficient integrability. -/
theorem coefficientInput_integrable_boundedVariation {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Icc (-1) 1)) (n : ℕ) :
    Integrable (fun x ↦ f x * (T ℝ n).eval x) classicalMeasureT := by
  have hfc : BoundedVariationOn (fun θ ↦ f (cos θ)) (Icc 0 π) :=
    ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_antitoneOn f cos antitoneOn_cos
      (fun θ _ ↦ ⟨neg_one_le_cos θ, cos_le_one θ⟩))
  apply integrable_classicalMeasureT_mul_T ⟨_, ?_⟩ n
  apply integrable_classicalMeasureT_of_cos
  exact hfc.intervalIntegrable (by simp [uIcc_of_le pi_pos.le])

/-- A function of bounded variation has Chebyshev coefficients bounded by
`2 Var(f) / (π n)` for positive indices. No continuity is required (ATAP 7.1). -/
theorem abs_coefficient_le_of_boundedVariation {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Icc (-1) 1)) {n : ℕ} (hn : n ≠ 0) :
    |(coefficient (n := n) ⟨f, coefficientInput_integrable_boundedVariation hf n⟩)| ≤ 2 * (eVariationOn f (Icc (-1) 1)).toReal / (π * n) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hvar : eVariationOn (fun θ ↦ f (cos θ)) (Icc 0 π) ≤
      eVariationOn f (Icc (-1) 1) :=
    eVariationOn.comp_le_of_antitoneOn f cos antitoneOn_cos
      (fun θ _ ↦ ⟨neg_one_le_cos θ, cos_le_one θ⟩)
  have hfc : BoundedVariationOn (fun θ ↦ f (cos θ)) (Icc 0 π) :=
    ne_top_of_le_ne_top hf hvar
  have hmul : LipschitzWith (n : ℝ≥0) (fun θ : ℝ ↦ (n : ℝ) * θ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hnpos.le, NNReal.coe_natCast]
    exact le_rfl
  have hsin := lipschitzWith_sin.comp hmul
  have hd (θ : ℝ) : HasDerivAt (fun θ : ℝ ↦ sin (n * θ))
      ((n : ℝ) * cos (n * θ)) θ := by
    convert ((hasDerivAt_id θ).const_mul (n : ℝ)).sin using 1 <;> simp [mul_comm]
  have hint : IntervalIntegrable (fun θ : ℝ ↦ (n : ℝ) * cos (n * θ)) volume 0 π :=
    (by fun_prop : Continuous (fun θ : ℝ ↦ (n : ℝ) * cos (n * θ))).intervalIntegrable 0 π
  have hi := hfc.abs_integral_mul_le_of_lipschitz_primitive pi_pos.le hsin
    (fun θ _ ↦ hd θ) hint (by simp) (sin_nat_mul_pi n) zero_le_one
    (fun θ _ ↦ abs_sin_le_one (n * θ))
  have heq : (∫ θ in 0..π, (n : ℝ) * cos (n * θ) * f (cos θ)) =
      n * ∫ θ in 0..π, f (cos θ) * cos (n * θ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [heq, abs_mul, abs_of_pos hnpos, one_mul] at hi
  have hV := ENNReal.toReal_mono hf hvar
  rw [coefficient_eq_integral_cos, ite_eq_right hn, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / π)]
  apply (le_div_iff₀ (mul_pos pi_pos hnpos)).2
  have hpi : π ≠ 0 := pi_pos.ne'
  field_simp
  nlinarith [hi.trans hV]

/-- The bounded-variation coefficient estimate with an explicit variation bound
(ATAP, Theorem 7.1 with smoothness index zero). -/
theorem abs_coefficient_le_of_eVariationOn_le {f : ℝ → ℝ} {V : ℝ}
    (hV : 0 ≤ V) (hf : eVariationOn f (Icc (-1) 1) ≤ ENNReal.ofReal V)
    {n : ℕ} (hn : n ≠ 0) : |(coefficient (n := n) ⟨f, coefficientInput_integrable_boundedVariation (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf) n⟩)| ≤ 2 * V / (π * n) := by
  have hfin : BoundedVariationOn f (Icc (-1) 1) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf
  apply (abs_coefficient_le_of_boundedVariation hfin hn).trans
  have hv : (eVariationOn f (Icc (-1) 1)).toReal ≤ V := by
    simpa only [ENNReal.toReal_ofReal hV] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hf
  gcongr

end Polynomial.Chebyshev
