/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Integration against a signed density

The bridge from signed-measure integration to the Bochner integral, used in
bounded-variation integration by parts for ATAP, Chapter 7.
-/

public section

open MeasureTheory

namespace MeasureTheory.VectorMeasure

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {μ : Measure X}

/-- Integrating a bounded function against an integrable real density agrees with
integrating its scalar product with that density. -/
theorem integral_withDensityᵥ_of_bound {f : X → ℝ} {g : X → E}
    (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    ∫ᵛ x, g x ∂<•(μ.withDensityᵥ f) = ∫ x, f x • g x ∂μ := by
  let := isFiniteMeasure_withDensity_ofReal hf.2
  let := isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hp : Integrable (fun x ↦ (ENNReal.ofReal (f x)).toReal • g x) μ := by
    simp only [ENNReal.toReal_ofReal']
    exact hf.pos_part.smul_bdd C hg hC
  have hn : Integrable (fun x ↦ (ENNReal.ofReal (-f x)).toReal • g x) μ := by
    simp only [ENNReal.toReal_ofReal']
    exact hf.neg_part.smul_bdd C hg hC
  have hp' : (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))).toSignedMeasure.Integrable g := by
    change Integrable g _
    rw [Measure.variation_toSignedMeasure]
    exact (integrable_withDensity_iff_integrable_smul₀' hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2 hp
  have hn' : (μ.withDensity (fun x ↦ ENNReal.ofReal (-f x))).toSignedMeasure.Integrable g := by
    change Integrable g _
    rw [Measure.variation_toSignedMeasure]
    exact (integrable_withDensity_iff_integrable_smul₀' hf.aestronglyMeasurable.aemeasurable.neg.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2 hn
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf,
    integral_sub_vectorMeasure hp' hn', integral_toSignedMeasure, integral_toSignedMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul₀ (f := fun x ↦ ENNReal.ofReal (-f x))
      hf.aestronglyMeasurable.aemeasurable.neg.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top), ← MeasureTheory.integral_sub hp hn]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [ENNReal.toReal_ofReal']
    exact (sub_smul (max (f x) 0) (max (-f x) 0) (g x)).symm.trans
      (congrArg (fun r : ℝ ↦ r • g x) (by grind))

/-- The signed-density integration identity restricted to a measurable set. -/
theorem setIntegral_withDensityᵥ_of_bound {f : X → ℝ} {g : X → E}
    (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) {s : Set X} (hs : MeasurableSet s) :
    ∫ᵛ x in s, g x ∂<•(μ.withDensityᵥ f) = ∫ x in s, f x • g x ∂μ := by
  rw [← VectorMeasure.integral_indicator hs]
  have hbound : ∀ᵐ x ∂μ, ‖s.indicator g x‖ ≤ max C 0 := by
    filter_upwards [hC] with x hx
    by_cases hxs : x ∈ s
    · simpa only [Set.indicator_of_mem hxs] using hx.trans (le_max_left C 0)
    · simp only [Set.indicator_of_notMem hxs, norm_zero, le_max_iff, le_refl, or_true]
  rw [integral_withDensityᵥ_of_bound hf (hg.indicator hs) hbound,
    ← MeasureTheory.integral_indicator hs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ s <;> simp [hx]

end MeasureTheory.VectorMeasure
