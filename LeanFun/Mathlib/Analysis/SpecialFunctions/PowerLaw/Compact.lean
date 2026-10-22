/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.SelfAdjoint
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.RegularizedKernel
public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousKernel
public import LeanFun.Mathlib.Analysis.IntegralEq.DominatedKernel

/-! # Compact power-law operators in the strict boundedness range

A slightly lower admissible power dominates the cutoff error in operator norm.
Continuous regularizations are compact; their norm limit is the original
operator. No compactness assertion is made on the critical boundary.
Reference: weakly singular kernel truncation and the Schur test.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Topology InnerProductSpace
namespace Real
variable {α lam : ℝ} (hlam : -(1/2) < lam)
local instance : NullSingletonClass (gegenbauerMeasure lam) := by
  exact nullSingletonClass_gegenbauerMeasure _

/-- Bounded L² realization of the continuous regularized kernel. -/
def regularizedPowerLawL2Operator (α : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam) := by
  let := isFiniteMeasure_gegenbauerMeasure hlam
  exact boundedKernelL2Operator _ _ (regularizedPowerLawKernel α ⟨δ,Or.inl hδ⟩)
    (continuous_regularizedPowerLawKernel α hδ).aestronglyMeasurable
    (show 0 ≤ δ^α + (2 : ℝ)^α by positivity)
    (Eventually.of_forall (norm_regularizedPowerLawKernel_le α hδ hδ2))

/-- Every positive-cutoff regularization is compact. -/
theorem isCompactOperator_regularizedPowerLawL2Operator (α : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    IsCompactOperator (regularizedPowerLawL2Operator hlam α hδ hδ2) := by
  let := isFiniteMeasure_gegenbauerMeasure hlam
  apply isCompactOperator_boundedKernelL2Operator_of_continuous _
    (continuous_regularizedPowerLawKernel α hδ) _
    (norm_regularizedPowerLawKernel_le α hδ hδ2) (powerLawHilbertBasis hlam) isCompact_Icc
  exact (ae_mem_Ioo_gegenbauerMeasure lam).mono (fun _ hx ↦ Ioo_subset_Icc_self hx)

/-- The lower-power domination gives an explicit operator-norm regularization error. -/
theorem norm_sub_regularizedPowerLawL2Operator_le
    (hα : -1 < α) (hs : -(1/2) ≤ α+lam) {β δ : ℝ}
    (hβ : -1 < β) (hβs : -(1/2) ≤ β+lam) (hβα : β < α) (hβ0 : β ≤ 0)
    (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    ‖boundedPowerLawL2Operator hα hlam hs - regularizedPowerLawL2Operator hlam α hδ hδ2‖ ≤
      (2*δ^(α-β))*‖boundedPowerLawL2Operator hβ hlam hβs‖ := by
  let := isFiniteMeasure_gegenbauerMeasure hlam
  let μ := gegenbauerMeasure lam
  obtain ⟨Ka,hKa,hea,_,hma⟩ := exists_powerLawKernel_density α
  obtain ⟨Kb,hKb,heb,_,hmb⟩ := exists_powerLawKernel_density β
  have hpair (e : ℝ) (he : -1 < e) (hes : -(1/2) ≤ e+lam)
      (K : ℝ × ℝ → ℝ≥0) (hK : Measurable K)
      (hm : powerLawKernelMeasure e lam = (μ.prod μ).withDensity (fun z ↦ (K z : ℝ≥0∞)))
      (f g : Lp ℝ 2 μ) :
      Integrable (fun z ↦ (K z : ℝ)*(g z.1*f z.2)) (μ.prod μ) ∧
      ⟪g,boundedPowerLawL2Operator he hlam hes f⟫_ℝ =
        ∫ z, (K z : ℝ)*(g z.1*f z.2) ∂μ.prod μ := by
    have h := boundedPowerLawL2Operator_spec he hlam hes f g
    constructor
    · rw [hm,integrable_withDensity_iff hK.coe_nnreal_ennreal (by simp)] at h
      simpa only [ENNReal.coe_toReal,smul_eq_mul,mul_comm] using h.1
    · rw [hm,integral_withDensity_eq_integral_toReal_smul hK.coe_nnreal_ennreal (by simp)] at h
      simpa only [ENNReal.coe_toReal,smul_eq_mul] using h.2
  have pa := hpair α hα hs Ka hKa (hma lam lam)
  have pb := hpair β hβ hβs Kb hKb (hmb lam lam)
  have ik := integrable_boundedKernelL2_pair μ μ (regularizedPowerLawKernel α ⟨δ,Or.inl hδ⟩)
    (continuous_regularizedPowerLawKernel α hδ).aestronglyMeasurable
    (show 0 ≤ δ^α + (2 : ℝ)^α by positivity)
    (Eventually.of_forall (norm_regularizedPowerLawKernel_le α hδ hδ2))
  apply norm_le_of_dominated_weak_kernel μ _ _
    (fun z ↦ (Ka z : ℝ) - regularizedPowerLawKernel α ⟨δ,Or.inl hδ⟩ z) (fun z ↦ (Kb z : ℝ))
  · intro f g
    apply (((pa f g).1).sub (ik f g)).congr
    filter_upwards [] with z
    change (Ka z : ℝ)*(g z.1*f z.2) - regularizedPowerLawKernel α ⟨δ,Or.inl hδ⟩ z*(g z.1*f z.2) = _
    ring
  · exact fun f g ↦ (pb f g).1
  · intro f g
    rw [sub_apply, inner_sub_right, (pa f g).2,
      regularizedPowerLawL2Operator, inner_boundedKernelL2Operator,
      ← integral_sub ((pa f g).1) (ik f g)]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  · exact fun f g ↦ (pb f g).2
  · positivity
  · filter_upwards [ae_mem_powerLawKernelDomain lam lam] with z hz
    rw [hea ⟨z,hz⟩,heb ⟨z,hz⟩]
    exact abs_sub_regularizedPowerLawKernel_le hβα hβ0 hδ
      (Ioo_subset_Icc_self hz.1) (Ioo_subset_Icc_self hz.2.1) hz.2.2

/-- Continuous cutoff operators converge in norm in the strict range. -/
theorem tendsto_regularizedPowerLawL2Operator (hα : -1 < α) (hs : -(1/2) < α+lam) :
    Tendsto (fun n : ℕ ↦ regularizedPowerLawL2Operator hlam α
      (show 0 < 1 / ((n : ℝ)+1) by positivity)
      (show 1 / ((n : ℝ)+1) ≤ 2 by rw [div_le_iff₀ (by positivity)]; nlinarith [Nat.cast_nonneg (α := ℝ) n]))
      atTop (𝓝 (boundedPowerLawL2Operator hα hlam hs.le)) := by
  obtain ⟨β, hb, hbs, hba, hb0⟩ := exists_lower_powerLaw_exponent hα hlam hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).rpow_const
    (Or.inr (sub_nonneg.mpr hba.le))
  have ht' : Tendsto (fun n : ℕ ↦
      (2*(1 / ((n : ℝ)+1))^(α-β))*‖boundedPowerLawL2Operator hb hlam hbs.le‖) atTop (𝓝 0) := by
    simpa only [zero_rpow (sub_pos.mpr hba).ne', mul_zero, zero_mul] using
      (ht.const_mul 2).mul_const ‖boundedPowerLawL2Operator hb hlam hbs.le‖
  apply squeeze_zero (fun _ ↦ norm_nonneg _) _ ht'
  intro n
  rw [norm_sub_rev]
  exact norm_sub_regularizedPowerLawL2Operator_le hlam hα hs.le hb hbs.le hba hb0.le _ _

/-- The weighted power-law operator is compact in the strict boundedness range. -/
theorem isCompactOperator_boundedPowerLawL2Operator (hα : -1 < α) (hs : -(1/2) < α+lam) :
    IsCompactOperator (boundedPowerLawL2Operator hα hlam hs.le) :=
  isCompactOperator_of_tendsto (tendsto_regularizedPowerLawL2Operator hlam hα hs)
    (Eventually.of_forall (fun _ ↦ isCompactOperator_regularizedPowerLawL2Operator hlam α _ _))

/-- Normalized coefficient coordinates preserve strict-range compactness. -/
theorem isCompactOperator_boundedPowerLawCoefficientOperator (hα : -1 < α)
    (hs : -(1/2) < α+lam) :
    IsCompactOperator (boundedPowerLawCoefficientOperator hα hlam hs.le) :=
  ((isCompactOperator_boundedPowerLawL2Operator hlam hα hs).comp_clm _).clm_comp _

/-- Leading normalized sections converge in operator norm in the strict range. -/
theorem tendsto_boundedPowerLawCoefficientOperator_sections_norm (hα : -1 < α)
    (hs : -(1/2) < α+lam) :
    Tendsto (fun n ↦ (lp.initialL2Projection n).comp
      ((boundedPowerLawCoefficientOperator hα hlam hs.le).comp (lp.initialL2Projection n)))
      atTop (𝓝 (boundedPowerLawCoefficientOperator hα hlam hs.le)) :=
  lp.tendsto_initialL2Sections_norm _ (isCompactOperator_boundedPowerLawCoefficientOperator hlam hα hs)

end Real
