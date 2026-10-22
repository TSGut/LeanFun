/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.CompactSections
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Compactness from continuous Hilbert-space kernel rows

Continuous rows on a compact support can be approximated uniformly by finite
coordinate projections. Their integral realization is therefore compact.
Reference: the finite-rank approximation proof of compactness of integral operators.
-/

public noncomputable section
open MeasureTheory Filter Set ContinuousLinearMap
open scoped ENNReal Topology InnerProductSpace
namespace MeasureTheory
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- An L² operator with continuous coefficient-space rows on compact support is compact. -/
theorem isCompactOperator_of_continuous_L2_rows
    (T : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] Lp ℝ 2 μ)
    (r : X → lp (fun _ : ℕ ↦ ℝ) 2) {S : Set X}
    (hS : IsCompact S) (hr : ContinuousOn r S) (hs : ∀ᵐ x ∂μ, x ∈ S)
    (hT : ∀ f, T f =ᵐ[μ] fun x ↦ ⟪r x, f⟫_ℝ) : IsCompactOperator T := by
  apply isClosed_setOfPred_isCompactOperator.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  let c : ℝ := (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hc : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  let δ := ε / (c + 1)
  have hd : 0 < δ := div_pos hε (by positivity)
  have hu := tendstoUniformlyOn_of_strongly_tendsto_id
    (lp.initialL2Projection (𝕜 := ℝ)) lp.norm_initialL2Projection_le
    lp.tendsto_initialL2Projection (hS.image_of_continuousOn hr)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.mp hu δ hd)
  refine ⟨T.comp (lp.initialL2Projection N),
    (lp.isCompactOperator_initialL2Projection N).clm_comp T, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  have hb : ‖T.comp (lp.initialL2Projection N) - T‖ ≤ c * δ := by
    apply opNorm_le_bound _ (mul_nonneg hc hd.le)
    intro f
    have ha : ∀ᵐ x ∂μ, ‖((T.comp (lp.initialL2Projection N) - T) f) x‖ ≤ δ * ‖f‖ := by
      filter_upwards [hs, hT (lp.initialL2Projection N f), hT f,
        Lp.coeFn_sub (T (lp.initialL2Projection N f)) (T f)] with x hx hp ht he
      change ‖(T (lp.initialL2Projection N f) - T f) x‖ ≤ _
      rw [he, Pi.sub_apply, hp, ht, ← lp.adjoint_initialL2Projection N,
        adjoint_inner_right, ← inner_sub_left]
      apply (norm_inner_le_norm _ _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [dist_eq_norm, id_eq, norm_sub_rev] using (hN N le_rfl (r x) ⟨x, hx, rfl⟩).le
    simpa only [mul_assoc] using Lp.norm_le_of_ae_bound (mul_nonneg hd.le (norm_nonneg f)) ha
  apply hb.trans_lt
  dsimp only [δ]
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < c + 1)]
  nlinarith

end MeasureTheory
