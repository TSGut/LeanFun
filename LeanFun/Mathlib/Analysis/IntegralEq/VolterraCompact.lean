/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraRows
public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousRows

/-! # Compact Volterra operators and norm-convergent coefficient sections

Continuous L² kernel rows yield compactness. Thus the normalized finite
sections converge in operator norm, not merely strongly on individual inputs.
Reference: Gutleb–Olver, arXiv:1906.03907, and compact finite-section theory.
-/

public noncomputable section
open MeasureTheory Polynomial Real Set Filter ContinuousLinearMap
open scoped Topology InnerProductSpace
namespace Real
variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
  {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |K z| ≤ M)

local instance : IsFiniteMeasure (unitJacobiMeasure 0 0) :=
  isFiniteMeasure_unitJacobiMeasure (by norm_num) (by norm_num)

/-- Every continuous triangle kernel gives a compact physical Volterra operator. -/
theorem isCompactOperator_volterraL2Operator :
    IsCompactOperator (volterraL2Operator hK hM hb) := by
  let b := hilbertBasisShiftedJacobi (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0)
  let S := (volterraL2Operator hK hM hb).comp
    b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hc : IsCompactOperator S := by
    apply isCompactOperator_of_continuous_L2_rows (unitJacobiMeasure 0 0) S
      (fun x ↦ (1/2 : ℝ) • b.repr (volterraL2Row hK hM hb x)) isCompact_Icc
    · exact (b.repr.continuous.comp_continuousOn
        (continuousOn_volterraL2Row hK hM hb)).const_smul (1/2 : ℝ)
    · exact ae_mem_Icc_unitJacobiMeasure 0 0
    · intro f
      filter_upwards [volterraL2Operator_ae_inner_row hK hM hb (b.repr.symm f)] with x hx
      change volterraL2Operator hK hM hb (b.repr.symm f) x = _
      rw [hx, real_inner_smul_left]
      congr 1
      rw [← b.repr.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  have he : S.comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap =
      volterraL2Operator hK hM hb := by
    apply ContinuousLinearMap.ext
    intro f
    change volterraL2Operator hK hM hb (b.repr.symm (b.repr f)) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [← he]
  exact hc.comp_clm _

/-- Normalized shifted Legendre coordinates preserve compactness. -/
theorem isCompactOperator_volterraL2CoefficientOperator :
    IsCompactOperator (volterraL2CoefficientOperator hK hM hb) :=
  ((isCompactOperator_volterraL2Operator hK hM hb).comp_clm _).clm_comp _

/-- Leading normalized Volterra sections converge in operator norm. -/
theorem tendsto_volterraL2CoefficientOperator_sections_norm :
    Tendsto (fun n ↦ (lp.initialL2Projection n).comp
      ((volterraL2CoefficientOperator hK hM hb).comp (lp.initialL2Projection n)))
      atTop (𝓝 (volterraL2CoefficientOperator hK hM hb)) :=
  lp.tendsto_initialL2Sections_norm _ (isCompactOperator_volterraL2CoefficientOperator hK hM hb)

end Real
