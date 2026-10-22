/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Compact
public import LeanFun.Mathlib.Analysis.IntegralEq.VanishingMultipliers

/-! # Sharp compactness threshold for weighted power-law operators

At the critical exponent, shrinking endpoint strips retain a fixed amount of
operator norm. This excludes compactness by dominated convergence of output
cutoffs. Reference: the endpoint scaling test for the power-law operators of
Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

public noncomputable section
open MeasureTheory Set Polynomial Filter
open scoped ENNReal InnerProductSpace Topology
namespace Real

private def endpointCutoff (n : ℕ) : ℝ → ℝ :=
  (Ioo (1-1/((n : ℝ)+1)) 1).indicator (fun _ ↦ 1)

private theorem endpointCutoff_measurable (n : ℕ) : Measurable (endpointCutoff n) :=
  measurable_const.indicator measurableSet_Ioo

private theorem norm_endpointCutoff_le (n : ℕ) (x : ℝ) : ‖endpointCutoff n x‖ ≤ 1 := by
  simp only [endpointCutoff, Set.indicator_apply]
  split_ifs <;> norm_num

private theorem tendsto_endpointCutoff (x : ℝ) :
    Tendsto (fun n ↦ endpointCutoff n x) atTop (𝓝 0) := by
  by_cases hx : x < 1
  · have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1-x by linarith))
    apply tendsto_const_nhds.congr'
    filter_upwards [ht] with n hn
    symm
    apply indicator_of_notMem
    simp only [mem_Ioo, not_and]
    intro hh
    linarith
  · have he : (fun n ↦ endpointCutoff n x) = fun _ ↦ 0 := by
      funext n
      exact indicator_of_notMem (fun h ↦ hx h.2) _
    rw [he]
    exact tendsto_const_nhds


theorem not_isCompactOperator_powerLaw_critical_of_pairing {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hc : α+lam = -(1/2))
    (T : Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam))
    (hT : ∀ f g : Lp ℝ 2 (gegenbauerMeasure lam),
      Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α lam) ∧
      ⟪g,T f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam) : ¬ IsCompactOperator T := by
  intro hcompact
  let μ := gegenbauerMeasure lam
  let := isFiniteMeasure_gegenbauerMeasure hlam
  obtain ⟨K,hK,hke⟩ := exists_powerLawWeakKernel α lam T hT
  let Q n := boundedMulL2 μ (endpointCutoff n)
    (endpointCutoff_measurable n).aestronglyMeasurable zero_le_one
    (Eventually.of_forall (norm_endpointCutoff_le n))
  have ht : Tendsto (fun n ↦ ‖(Q n).comp T‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using
      (tendsto_boundedMulL2_comp_compact_zero μ endpointCutoff
        (fun n ↦ (endpointCutoff_measurable n).aestronglyMeasurable) zero_le_one
        (fun n ↦ Eventually.of_forall (norm_endpointCutoff_le n))
        (Eventually.of_forall tendsto_endpointCutoff) T hcompact).norm
  have hl (n : ℕ) : (2 : ℝ)^(lam-1/2)/4 ≤ ‖(Q n).comp T‖ := by
    let Kn : L2WeakKernel μ := L2WeakKernel.ofSFinite
      (fun z ↦ endpointCutoff n z.1*K.kernel z) ((Q n).comp K.operator)
      (fun f g ↦ (inner_boundedMulL2_comp_kernel μ K (endpointCutoff n)
        (endpointCutoff_measurable n).aestronglyMeasurable zero_le_one
        (Eventually.of_forall (norm_endpointCutoff_le n)) f g).1)
      (fun f g ↦ (inner_boundedMulL2_comp_kernel μ K (endpointCutoff n)
        (endpointCutoff_measurable n).aestronglyMeasurable zero_le_one
        (Eventually.of_forall (norm_endpointCutoff_le n)) f g).2)
    have hh := powerLaw_endpoint_scaling_le_norm_of_agreesOn
      ⟨α,by change α ≤ 0; linarith⟩ ⟨lam,hlam,by change lam ≤ 1/2; linarith⟩
      ⟨1/((n : ℝ)+1),by positivity,
        by rw [div_le_iff₀ (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]⟩
      Kn (by
        intro z
        change endpointCutoff n z.val.1*K.kernel z.val = _
        rw [endpointCutoff,indicator_of_mem z.property.1,one_mul]
        exact hke ⟨z.val,z.property.2.2⟩)
    have he : α+lam+1/2 = 0 := by linarith
    simpa only [Kn,L2WeakKernel.ofSFinite,he,rpow_zero,mul_one,hK] using hh
  have hp : 0 < (2 : ℝ)^(lam-1/2)/4 := by positivity
  exact (not_le_of_gt hp) (ge_of_tendsto ht (Eventually.of_forall hl))

/-- Compactness holds exactly in the strict part of the same-space boundedness range. -/
theorem isCompactOperator_boundedPowerLawL2Operator_iff {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam) :
    IsCompactOperator (boundedPowerLawL2Operator hα hlam hs) ↔ -(1/2) < α+lam := by
  constructor
  · intro h
    rcases hs.eq_or_lt with he | he
    · exact False.elim (not_isCompactOperator_powerLaw_critical_of_pairing hα hlam he.symm _
        (boundedPowerLawL2Operator_spec hα hlam hs) h)
    · exact he
  · exact isCompactOperator_boundedPowerLawL2Operator hlam hα

/-- The normalized coefficient operator has the same sharp compactness threshold. -/
theorem isCompactOperator_boundedPowerLawCoefficientOperator_iff {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam) :
    IsCompactOperator (boundedPowerLawCoefficientOperator hα hlam hs) ↔ -(1/2) < α+lam := by
  constructor
  · intro h
    let b := powerLawHilbertBasis hlam
    have hh := (h.comp_clm b.repr.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap
    have he : b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((boundedPowerLawCoefficientOperator hα hlam hs).comp
          b.repr.toContinuousLinearEquiv.toContinuousLinearMap) =
        boundedPowerLawL2Operator hα hlam hs := by
      apply ContinuousLinearMap.ext
      intro f
      simp [boundedPowerLawCoefficientOperator, HilbertBasis.coefficientOperator, b]
    change IsCompactOperator (b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((boundedPowerLawCoefficientOperator hα hlam hs).comp
        b.repr.toContinuousLinearEquiv.toContinuousLinearMap)) at hh
    rw [he] at hh
    exact (isCompactOperator_boundedPowerLawL2Operator_iff hα hlam hs).mp hh
  · exact isCompactOperator_boundedPowerLawCoefficientOperator hlam hα

end Real
