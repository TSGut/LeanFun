/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

import Mathlib.Topology.Algebra.Polynomial

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.SmoothDecay
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Derivative relations for Chebyshev coefficients

The integration step in ATAP, Theorem 7.1, with an absolutely continuous
function and an almost-everywhere derivative representative.
-/

public section

namespace Polynomial.Chebyshev

open Real Set MeasureTheory intervalIntegral Filter
open scoped Topology

private theorem cosine_pullback_eq_integral {f g : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f (-1) 1)
    (hd : ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt f (g x) x)
    {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    f (cos θ) = f 1 + ∫ t in 0..θ, g (cos t) * (-sin t) := by
  have hsub : uIcc (cos θ) 1 ⊆ uIcc (-1 : ℝ) 1 := by
    rw [uIcc_of_le (cos_le_one θ), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (neg_one_le_cos θ) le_rfl
  obtain ⟨q⟩ := IntegrableDerivative.nonempty_of_absolutelyContinuous hf
  have hd' : ∀ᵐ x ∂volume.restrict (uIcc (-1 : ℝ) 1), HasDerivAt f (g x) x := by
    rw [ae_restrict_iff' measurableSet_uIcc]
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hd
  have he : (q : ℝ → ℝ) =ᵐ[volume.restrict (uIcc (-1 : ℝ) 1)] g := by
    filter_upwards [q.hasDerivAt, hd'] with x hx hy
    exact hx.unique hy
  have hi : IntegrableOn g (uIcc (-1 : ℝ) 1) volume := q.integrable.congr he
  let d : IntegrableDerivative f (volume.restrict (uIcc (cos θ) 1)) :=
    ⟨⟨g, hi.mono_set hsub⟩, ae_restrict_of_ae_restrict_of_subset hsub hd'⟩
  have hFTC := d.integral_eq_sub (hf.mono hsub)
  change (∫ x in cos θ..1, g x) = f 1 - f (cos θ) at hFTC
  have hchange := integral_comp_mul_deriv_of_deriv_nonpos
    (a := 0) (b := θ) (f := cos) (f' := fun t ↦ -sin t) (g := g)
    (by fun_prop) (fun t _ ↦ hasDerivAt_cos t)
    (fun t ht ↦ by
      simp only [min_eq_left hθ.1, max_eq_right hθ.1] at ht
      exact neg_nonpos.mpr (sin_nonneg_of_nonneg_of_le_pi ht.1.le (ht.2.le.trans hθ.2)))
  simp only [cos_zero, Function.comp_apply] at hchange
  rw [hchange, integral_symm]
  linarith

/-- The cosine pullback of an absolutely continuous function is absolutely
continuous when the supplied derivative representative has an integrable cosine
pullback. The derivative identity is retained almost everywhere. -/
theorem absolutelyContinuous_cosine_pullback {f g : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f (-1) 1)
    (hd : ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt f (g x) x)
    (hg : IntervalIntegrable (fun θ ↦ g (cos θ)) volume 0 π) :
    AbsolutelyContinuousOnInterval (fun θ ↦ f (cos θ)) 0 π ∧
      ∀ᵐ θ ∂volume, θ ∈ Icc 0 π →
        HasDerivAt (fun θ ↦ f (cos θ)) (g (cos θ) * (-sin θ)) θ := by
  let H : ℝ → ℝ := fun θ ↦ g (cos θ) * (-sin θ)
  have hH : IntervalIntegrable H volume 0 π := hg.mul_continuousOn (by fun_prop)
  let J : ℝ → ℝ := (uIcc 0 π).indicator H
  have hJ : Integrable J := (integrable_indicator_iff measurableSet_uIcc).mpr
    ((intervalIntegrable_iff').mp hH)
  have heq : EqOn (fun θ ↦ f 1 + ∫ t in 0..θ, J t) (fun θ ↦ f (cos θ)) (Icc 0 π) := by
    intro θ hθ
    have he : (∫ t in 0..θ, J t) = ∫ t in 0..θ, H t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hm : t ∈ uIcc 0 π := by
        rw [uIcc_of_le pi_pos.le]
        rw [uIcc_of_le hθ.1] at ht
        exact ⟨ht.1, ht.2.trans hθ.2⟩
      exact Set.indicator_of_mem hm H
    change f 1 + (∫ t in 0..θ, J t) = f (cos θ)
    rw [he]
    exact (cosine_pullback_eq_integral hf hd hθ).symm
  have hac := hJ.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (a := 0) (b := π) (c := 0) (by simp)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ f 1) 0 π :=
    (show ContDiff ℝ 1 (fun _ : ℝ ↦ f 1) by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  constructor
  · exact (hc.fun_add hac).congr (by simpa only [uIcc_of_le pi_pos.le] using heq)
  · filter_upwards [(hJ.intervalIntegrable (a := 0) (b := π)).ae_hasDerivAt_integral,
      (countable_singleton (0 : ℝ)).ae_notMem volume,
      (countable_singleton π).ae_notMem volume] with θ hθ hzero hpi hmem
    have hθ' : θ ∈ Ioo 0 π := by simpa using (show 0 < θ ∧ θ < π by grind)
    have hder := (hθ (by simpa only [uIcc_of_le pi_pos.le] using hmem) 0 (by simp)).const_add (f 1)
    have hm : θ ∈ uIcc 0 π := by simpa only [uIcc_of_le pi_pos.le] using hmem
    simp only [J, Set.indicator_of_mem hm] at hder
    apply hder.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hθ'.1 hθ'.2] with t ht
    exact (heq (Ioo_subset_Icc_self ht)).symm

/-- Adjacent coefficients of the derivative determine a positive-degree
coefficient of an absolutely continuous function (ATAP, Chapter 7).
The indices start at two because the constant coefficient has a different normalization. -/
theorem coefficient_eq_sub_derivative_coefficients {f g : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f (-1) 1)
    (hd : ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt f (g x) x)
    (hg : IntervalIntegrable (fun θ ↦ g (cos θ)) volume 0 π) (n : ℕ) :
    (coefficient (n := (n + 2)) ⟨f, by
      apply integrable_classicalMeasureT
      have hc : ContinuousOn f (Icc (-1) 1) := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hf.continuousOn
      exact hc.mul (by fun_prop)⟩) =
      ((coefficient (n := (n + 1)) ⟨g, integrable_classicalMeasureT_mul_T ⟨g, integrable_classicalMeasureT_of_cos hg⟩ _⟩) - (coefficient (n := (n + 3)) ⟨g, integrable_classicalMeasureT_mul_T ⟨g, integrable_classicalMeasureT_of_cos hg⟩ _⟩)) / (2 * (n + 2 : ℕ)) := by
  obtain ⟨hac, hder⟩ := absolutelyContinuous_cosine_pullback hf hd hg
  let d : IntegrableDerivative (fun θ ↦ f (cos θ)) (volume.restrict (uIcc 0 π)) :=
    ⟨⟨fun θ ↦ g (cos θ) * (-sin θ),
      (intervalIntegrable_iff').mp (hg.mul_continuousOn (by fun_prop))⟩, by
      rw [ae_restrict_iff' measurableSet_uIcc]
      simpa only [uIcc_of_le pi_pos.le] using hder⟩
  rw [coefficient_eq_integral_sin_of_absolutelyContinuous hac d (by omega)]
  dsimp only [d]
  have htrig (θ : ℝ) : (g (cos θ) * (-sin θ)) * sin ((n + 2 : ℕ) * θ) =
      -(1 / 2 : ℝ) * (g (cos θ) * cos ((n + 1 : ℕ) * θ) -
        g (cos θ) * cos ((n + 3 : ℕ) * θ)) := by
    have ht := two_mul_sin_mul_sin ((n + 2 : ℕ) * θ) θ
    have hminus : ((n + 2 : ℕ) : ℝ) * θ - θ = (n + 1 : ℕ) * θ := by push_cast; ring
    have hplus : ((n + 2 : ℕ) : ℝ) * θ + θ = (n + 3 : ℕ) * θ := by push_cast; ring
    rw [hminus, hplus] at ht
    linear_combination -(g (cos θ) / 2) * ht
  simp_rw [htrig]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hg.mul_continuousOn (by fun_prop))
      (hg.mul_continuousOn (by fun_prop)),
    coefficient_eq_integral_cos, coefficient_eq_integral_cos,
    ite_eq_right (show n + 1 ≠ 0 by omega), ite_eq_right (show n + 3 ≠ 0 by omega)]
  ring

/-- The exceptional first-degree recurrence uses the full constant coefficient:
`a₁ = b₀ - b₂/2` for the derivative coefficients `b` (ATAP, Chapter 7). -/
theorem coefficient_one_eq_derivative_coefficients {f g : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f (-1) 1)
    (hd : ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt f (g x) x)
    (hg : IntervalIntegrable (fun θ ↦ g (cos θ)) volume 0 π) :
    (coefficient (n := 1) ⟨f, by
      apply integrable_classicalMeasureT
      have hc : ContinuousOn f (Icc (-1) 1) := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hf.continuousOn
      exact hc.mul (by fun_prop)⟩) = (coefficient (n := 0) ⟨g, integrable_classicalMeasureT_mul_T ⟨g, integrable_classicalMeasureT_of_cos hg⟩ _⟩) - (coefficient (n := 2) ⟨g, integrable_classicalMeasureT_mul_T ⟨g, integrable_classicalMeasureT_of_cos hg⟩ _⟩) / 2 := by
  obtain ⟨hac, hder⟩ := absolutelyContinuous_cosine_pullback hf hd hg
  let d : IntegrableDerivative (fun θ ↦ f (cos θ)) (volume.restrict (uIcc 0 π)) :=
    ⟨⟨fun θ ↦ g (cos θ) * (-sin θ),
      (intervalIntegrable_iff').mp (hg.mul_continuousOn (by fun_prop))⟩, by
      rw [ae_restrict_iff' measurableSet_uIcc]
      simpa only [uIcc_of_le pi_pos.le] using hder⟩
  rw [coefficient_eq_integral_sin_of_absolutelyContinuous hac d (by norm_num : 1 ≠ 0)]
  dsimp only [d]
  have htrig (θ : ℝ) : (g (cos θ) * (-sin θ)) * sin ((1 : ℕ) * θ) =
      -(1 / 2 : ℝ) * (g (cos θ) - g (cos θ) * cos (2 * θ)) := by
    have ht := two_mul_sin_mul_sin θ θ
    simp only [sub_self, cos_zero, ← two_mul] at ht
    simp only [Nat.cast_one, one_mul]
    linear_combination -(g (cos θ) / 2) * ht
  simp_rw [htrig]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hg (hg.mul_continuousOn (by fun_prop)),
    coefficient_eq_integral_cos, coefficient_eq_integral_cos]
  norm_num
  ring

end Polynomial.Chebyshev
