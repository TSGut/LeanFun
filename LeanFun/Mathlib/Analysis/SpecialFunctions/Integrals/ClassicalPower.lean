/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-! # Classical real-power primitives
Positive-base powers and polynomial integer powers have separate domains.
These supply the elementary integrations in Gutleb--Carrillo--Olver,
arXiv:2011.00045, Section2.
-/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace Real
/-- Real powers are integrated only at positive bases; endpoints may be zero. -/
theorem integrable_rpow_openInterval (α : Ioi (-1 : ℝ)) (a b : ℝ≥0) :
    Integrable (fun t : Ioo (min (a : ℝ) (b : ℝ)) (max (a : ℝ) (b : ℝ)) ↦ t.val^α.val)
      (Measure.comap Subtype.val volume) := by
  apply (integrableOn_iff_comap_subtypeVal (f := fun t : ℝ ↦ t ^ α.val) measurableSet_Ioo).mp
  by_cases h : 0 < max (a : ℝ) (b : ℝ)
  · exact ((intervalIntegral.integrableOn_Ioo_rpow_iff h).2 α.property).mono_set
      (Ioo_subset_Ioo (le_min a.property b.property) le_rfl)
  · have he : Ioo (min (a : ℝ) (b : ℝ)) (max (a : ℝ) (b : ℝ)) = ∅ :=
      Ioo_eq_empty_of_le ((le_of_not_gt h).trans (le_min a.property b.property))
    rw [he]
    exact integrableOn_empty
/-- All bases in this integration domain are strictly positive. -/
theorem rpow_openInterval_base_pos (a b : ℝ≥0)
    (t : Ioo (min (a : ℝ) (b : ℝ)) (max (a : ℝ) (b : ℝ))) : 0 < t.val :=
  (le_min a.property b.property).trans_lt t.property.1
private theorem positive_primitive (α : Ioi (-1 : ℝ)) (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ t : Ioo (a : ℝ) b, t.val^α.val ∂Measure.comap Subtype.val volume) =
      ((b : ℝ)^(α.val+1)-(a : ℝ)^(α.val+1))/(α.val+1) := by
  have hr : (a : ℝ) ≤ (b : ℝ) := hab
  have hα : -1 < α.val := α.property
  let P : ℝ → ℝ := fun t ↦ if 0 < t then t^α.val else 0
  let F : ℝ → ℝ := fun t ↦ ((t.toNNReal ^ (α.val+1) : ℝ≥0) : ℝ)/(α.val+1)
  have he (t : ℝ) (ht : 0 < t) : P t = t^α.val := by simp only [P, ite_eq_left ht]
  have hF (t : ℝ) (ht : 0 ≤ t) : F t = t^(α.val+1)/(α.val+1) := by
    simp only [F,NNReal.coe_rpow,Real.coe_toNNReal t ht]
  have hc : Continuous F :=
    (NNReal.continuous_coe.comp ((NNReal.continuous_rpow_const
      (by linarith [hα] : 0 ≤ α.val+1)).comp continuous_real_toNNReal)).div_const _
  have hi : IntervalIntegrable P volume a b := by
    erw [intervalIntegrable_iff_integrableOn_Ioo_of_le (f := P) (μ := volume) hab]
    apply (integrableOn_iff_comap_subtypeVal (f := P) (μ := volume) measurableSet_Ioo).mpr
    have h := integrable_rpow_openInterval α a b
    erw [min_eq_left hr, max_eq_right hr] at h
    apply h.congr
    filter_upwards [] with t
    exact (he t.val (a.coe_nonneg.trans_lt t.property.1)).symm
  have hd (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) : HasDerivAt F (P t) t := by
    have hp : 0 < t := a.coe_nonneg.trans_lt ht.1
    have hh := (hasDerivAt_rpow_const (p := α.val+1) (Or.inl hp.ne')).div_const (α.val+1)
    have hf : F =ᶠ[𝓝 t] (fun s : ℝ ↦ s^(α.val+1)/(α.val+1)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hp] with s hs
      exact hF s hs.le
    have hh' := hh.congr_of_eventuallyEq hf
    rw [he t hp]
    simpa only [add_sub_cancel_right, mul_div_cancel_left₀ _
      (by linarith [hα] : α.val+1 ≠ 0)] using hh'
  have hj := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc.continuousOn hd hi
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ← integral_subtype_comap measurableSet_Ioo P] at hj
  calc
    _ = ∫ t : Ioo (a : ℝ) b, P t.val ∂Measure.comap Subtype.val volume := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact (he t.val (a.coe_nonneg.trans_lt t.property.1)).symm
    _ = F b - F a := hj
    _ = _ := by rw [hF b b.coe_nonneg,hF a a.coe_nonneg]; ring

/-- The oriented primitive formula on nonnegative endpoints, using an open integration domain. -/
theorem integral_rpow_openInterval (α : Ioi (-1 : ℝ)) (a b : ℝ≥0) :
    (if a ≤ b then (1 : ℝ) else -1) *
      (∫ t : Ioo (min (a : ℝ) (b : ℝ)) (max (a : ℝ) (b : ℝ)),
        t.val^α.val ∂Measure.comap Subtype.val volume) =
      ((b : ℝ)^(α.val+1)-(a : ℝ)^(α.val+1))/(α.val+1) := by
  by_cases h : a ≤ b
  · have hr : (a : ℝ) ≤ (b : ℝ) := h
    erw [ite_eq_left h,min_eq_left hr,max_eq_right hr,one_mul]
    exact positive_primitive α a b h
  · have hr : (b : ℝ) ≤ (a : ℝ) := le_of_lt (lt_of_not_ge h)
    erw [ite_eq_right h,min_eq_right hr,max_eq_left hr]
    rw [positive_primitive α b a (le_of_lt (lt_of_not_ge h))]
    ring
/-- Integer powers also have their classical primitive on arbitrary real intervals. -/
theorem integral_natPow_classical (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ t^n) volume a b ∧
    (∫ t in a..b, t^n) = (b^(n+1)-a^(n+1))/(n+1) := by
  exact ⟨(continuous_id.pow n).intervalIntegrable _ _, integral_pow n⟩
end Real
