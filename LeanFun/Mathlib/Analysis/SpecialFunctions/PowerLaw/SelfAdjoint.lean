/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.FullCoefficients
public import LeanFun.Mathlib.Analysis.InnerProductSpace.CompactSections

/-! # Self-adjoint weighted power-law operators

Symmetry of the weak kernel gives self-adjointness on the entire boundedness
range, including its critical boundary. Reference: Gutleb–Carrillo–Olver,
arXiv:2011.00045, §2 (integral operators only).
-/

public noncomputable section
open MeasureTheory Polynomial Set
open scoped ENNReal NNReal InnerProductSpace
namespace Real
variable {α lam : ℝ} (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam)

/-- Symmetry of the weak kernel holds for every pair of weighted L² vectors. -/
theorem inner_boundedPowerLawL2Operator_symm
    (f g : Lp ℝ 2 (gegenbauerMeasure lam)) :
    ⟪g, boundedPowerLawL2Operator hα hlam hs f⟫_ℝ =
      ⟪f, boundedPowerLawL2Operator hα hlam hs g⟫_ℝ := by
  let := isFiniteMeasure_gegenbauerMeasure hlam
  obtain ⟨K,hK,he,hz,hμ⟩ := exists_powerLawKernel_density α
  have hsym (z : ℝ × ℝ) : K z.swap = K z := by
    by_cases h : z.1 ∈ Ioo (-1 : ℝ) 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 1 ∧ z.1 ≠ z.2
    · apply NNReal.eq
      rw [he ⟨z,h⟩,he ⟨z.swap,h.2.1,h.1,h.2.2.symm⟩]
      change |z.2-z.1|^α = |z.1-z.2|^α
      rw [abs_sub_comm]
    · rw [hz z h,hz z.swap (fun hs ↦ h ⟨hs.2.1,hs.1,hs.2.2.symm⟩)]
  have hm : powerLawKernelMeasure α lam =
      ((gegenbauerMeasure lam).prod (gegenbauerMeasure lam)).withDensity
        (fun z ↦ (K z : ℝ≥0∞)) := hμ lam lam
  rw [(boundedPowerLawL2Operator_spec hα hlam hs f g).2,(boundedPowerLawL2Operator_spec hα hlam hs g f).2,hm,
    integral_withDensity_eq_integral_toReal_smul hK.coe_nnreal_ennreal (by simp),
    integral_withDensity_eq_integral_toReal_smul hK.coe_nnreal_ennreal (by simp)]
  rw [← integral_prod_swap]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [ENNReal.coe_toReal,smul_eq_mul,Prod.swap,mul_comm]
  rw [show K (z.2,z.1) = K z from hsym z]

/-- The weighted operator is self-adjoint throughout the exact boundedness range. -/
theorem isSelfAdjoint_boundedPowerLawL2Operator :
    IsSelfAdjoint (boundedPowerLawL2Operator hα hlam hs) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  rw [real_inner_comm]
  exact inner_boundedPowerLawL2Operator_symm hα hlam hs f g

/-- Normalized Chebyshev/Gegenbauer coefficient transport preserves self-adjointness. -/
theorem isSelfAdjoint_boundedPowerLawCoefficientOperator :
    IsSelfAdjoint (boundedPowerLawCoefficientOperator hα hlam hs) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  let b := powerLawHilbertBasis hlam
  change ⟪b.repr (boundedPowerLawL2Operator hα hlam hs (b.repr.symm f)), g⟫_ℝ =
    ⟪f, b.repr (boundedPowerLawL2Operator hα hlam hs (b.repr.symm g))⟫_ℝ
  rw [← b.repr.apply_symm_apply g, ← b.repr.apply_symm_apply f]
  simp only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]
  rw [real_inner_comm]
  exact inner_boundedPowerLawL2Operator_symm hα hlam hs _ _

end Real
