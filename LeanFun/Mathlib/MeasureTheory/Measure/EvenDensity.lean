/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Even measures and even densities

Reflection invariance is preserved by symmetric restriction and even density.
These facts supply parity hypotheses in polynomial measure modification.
-/

public section
open Set
open scoped ENNReal
namespace MeasureTheory

/-- An even density preserves reflection invariance of a real measure. -/
theorem isNegInvariant_withDensity {μ : Measure ℝ} [μ.IsNegInvariant]
    (f : ℝ → ℝ≥0∞) (hf : ∀ x, f (-x) = f x) : (μ.withDensity f).IsNegInvariant := by
  constructor
  rw [Measure.neg_def]
  ext s hs
  rw [Measure.map_apply measurable_neg hs,
    withDensity_apply f (hs.preimage measurable_neg), withDensity_apply f hs,
    ← lintegral_indicator (hs.preimage measurable_neg), ← lintegral_indicator hs]
  have he : (Neg.neg ⁻¹' s).indicator f = fun x => s.indicator f (-x) := by
    funext x
    by_cases hx : -x ∈ s <;> simp [Set.indicator, hx, hf]
  rw [he, lintegral_neg_eq_self]

/-- Restriction to a reflection-invariant measurable set preserves evenness. -/
theorem isNegInvariant_restrict {μ : Measure ℝ} [μ.IsNegInvariant]
    {s : Set ℝ} (hs : MeasurableSet s) (he : Neg.neg ⁻¹' s = s) :
    (μ.restrict s).IsNegInvariant := by
  constructor
  rw [Measure.neg_def]
  simpa only [he] using ((Measure.measurePreserving_neg μ).restrict_preimage hs).map_eq

end MeasureTheory
