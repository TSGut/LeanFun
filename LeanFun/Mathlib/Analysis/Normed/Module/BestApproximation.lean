/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Best approximation in a finite-dimensional subspace
Compactness gives a nearest point without an inner-product assumption.
Reference: ATAP, Theorem 10.1, existence argument.
-/

public section
namespace Submodule

/-- A finite-dimensional subspace of a normed space over a proper field has a
best approximant. No strict convexity or uniqueness is asserted (ATAP 10.1). -/
theorem exists_norm_sub_le_of_finiteDimensional
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (V : Submodule 𝕜 E) [FiniteDimensional 𝕜 V] (f : E) :
    ∃ p : V, ∀ q : V, ‖f - (p : E)‖ ≤ ‖f - (q : E)‖ := by
  let : ProperSpace V := FiniteDimensional.proper 𝕜 V
  obtain ⟨p, hp, hmin⟩ := (isCompact_closedBall (0 : V) (2 * ‖f‖)).exists_isMinOn
    (⟨0, by simp [norm_nonneg]⟩ : (Metric.closedBall (0 : V) (2 * ‖f‖)).Nonempty)
    (show ContinuousOn (fun q : V ↦ ‖f - (q : E)‖) _ from
      (continuous_const.sub continuous_subtype_val).norm.continuousOn)
  refine ⟨p, fun q ↦ ?_⟩
  by_cases hq : q ∈ Metric.closedBall (0 : V) (2 * ‖f‖)
  · exact hmin hq
  · have hzero := hmin (show (0 : V) ∈ Metric.closedBall 0 (2 * ‖f‖) by simp [norm_nonneg])
    have hq' : 2 * ‖f‖ < ‖(q : E)‖ := by simpa using hq
    have ht : ‖(q : E)‖ ≤ ‖f‖ + ‖f - (q : E)‖ := by
      simpa only [sub_sub_cancel, norm_neg, norm_sub_rev] using norm_sub_le f (f - (q : E))
    change ‖f - (p : E)‖ ≤ ‖f - ((0 : V) : E)‖ at hzero
    simp only [ZeroMemClass.coe_zero, sub_zero] at hzero
    linarith

end Submodule
