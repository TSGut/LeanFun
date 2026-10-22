/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Measure
public import LeanFun.Mathlib.MeasureTheory.Measure.EvenDensity
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Reflection invariance of symmetric Jacobi measures

Reference: DLMF Table 18.3.1; symmetric Cartesian disk factors in Dunkl–Xu.
-/

public section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace Polynomial

/-- Symmetric Jacobi measures are even, independently of integrability assumptions. -/
theorem isNegInvariant_jacobiMeasure (α : ℝ) : (jacobiMeasure α α).IsNegInvariant := by
  classical
  let g : ℝ → ℝ≥0∞ := fun x ↦ if h : x ∈ Ioo (-1 : ℝ) 1 then
    (jacobiWeight α α ⟨x, h⟩ : ℝ≥0∞) else 0
  have hg : Measurable g :=
    ((measurable_jacobiWeight α α).coe_nnreal_ennreal).dite measurable_const measurableSet_Ioo
  have hm : jacobiMeasure α α = (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity g := by
    apply openIntervalWeightMeasure_eq _ _ _ _ hg
    intro x
    simp only [g, dite_eq_left x.property]
  rw [hm]
  have he : Neg.neg ⁻¹' Ioo (-1 : ℝ) 1 = Ioo (-1 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  let := isNegInvariant_restrict (μ := volume) measurableSet_Ioo he
  apply isNegInvariant_withDensity
  intro x
  have hn : -x ∈ Ioo (-1 : ℝ) 1 ↔ x ∈ Ioo (-1 : ℝ) 1 := by
    change x ∈ Neg.neg ⁻¹' Ioo (-1 : ℝ) 1 ↔ _
    rw [he]
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · simp only [g, dite_eq_left hx, dite_eq_left (hn.mpr hx)]
    congr 1
    apply NNReal.eq
    simp [jacobiWeight_apply, sub_eq_add_neg, mul_comm]
  · simp only [g, dite_eq_right hx, dite_eq_right (fun h ↦ hx (hn.mp h))]

end Polynomial
