/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LeanFun.Mathlib.Analysis.SpecialFunctions.Integrals.ClassicalPower
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.ContinuousMap.Basic

/-! # One-dimensional power-law integral operators

The plain kernel is used before any Gamma normalization. Left and right pieces
are kept separate, with explicit integrability hypotheses. The constant-input
formula includes both endpoints for exponent greater than -1.
Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Real







end Real

namespace Real
/-- The integration points of the power-law kernel, excluding its possible singularity. -/
abbrev PowerLawDomain (x : ℝ) := {y : ℝ // y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x}
/-- A weighted input belongs to the domain exactly when its power-law integral exists. -/
abbrev PowerLawInput (α x : ℝ) := {f : PowerLawDomain x → ℝ //
  Integrable (fun y ↦ |x-y.val|^α * f y) (Measure.comap Subtype.val volume)}
/-- The integral on the full weighted-integrability domain; the diagonal has no assigned value. -/
def powerLawIntegral {α x : ℝ} (f : PowerLawInput α x) : ℝ :=
  ∫ y : PowerLawDomain x, |x-y.val|^α * f.val y ∂Measure.comap Subtype.val volume
/-- Every kernel base is strictly positive. -/
theorem powerLawDomain_base_pos {x : ℝ} (y : PowerLawDomain x) : 0 < |x-y.val| :=
  abs_pos.mpr (sub_ne_zero.mpr y.property.2.symm)
/-- Characterization includes actual integrability, not a default integral value. -/
theorem powerLawIntegral_spec {α x : ℝ} (f : PowerLawInput α x) :
    Integrable (fun y : PowerLawDomain x ↦ |x-y.val|^α*f.val y)
      (Measure.comap Subtype.val volume) ∧
    powerLawIntegral f =
      ∫ y : PowerLawDomain x, |x-y.val|^α*f.val y ∂Measure.comap Subtype.val volume :=
  ⟨f.property, rfl⟩
end Real
namespace Real
/-- The punctured interval is measurable. -/
theorem measurableSet_powerLawDomain (x : ℝ) :
    MeasurableSet {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x} :=
  measurableSet_Ioo.inter (measurableSet_singleton x).compl


end Real
namespace Real
/-- Integrable inputs for the left-oriented positive-base kernel. -/
abbrev PowerLawLeftInput (α : ℝ) (x : Ici (-1 : ℝ)) :=
  {f : Ioo (-1 : ℝ) x.val → ℝ // Integrable (fun y ↦ (x.val-y.val)^α*f y)
    (Measure.comap Subtype.val volume)}
/-- Integrable inputs for the right-oriented positive-base kernel. -/
abbrev PowerLawRightInput (α : ℝ) (x : Iic (1 : ℝ)) :=
  {f : Ioo x.val (1 : ℝ) → ℝ // Integrable (fun y ↦ (y.val-x.val)^α*f y)
    (Measure.comap Subtype.val volume)}
def powerLawLeft {α : ℝ} {x : Ici (-1 : ℝ)} (f : PowerLawLeftInput α x) : ℝ :=
  ∫ y : Ioo (-1 : ℝ) x.val, (x.val-y.val)^α*f.val y ∂Measure.comap Subtype.val volume
def powerLawRight {α : ℝ} {x : Iic (1 : ℝ)} (f : PowerLawRightInput α x) : ℝ :=
  ∫ y : Ioo x.val (1 : ℝ), (y.val-x.val)^α*f.val y ∂Measure.comap Subtype.val volume



end Real
namespace Real
private theorem positive_power_data (α : Ioi (-1 : ℝ)) :
    ∃ P : ℝ → ℝ, (∀ t : ℝ, 0 < t → P t = t^α.val) ∧
      ∀ b : ℝ≥0, IntervalIntegrable P volume 0 b ∧
        (∫ t in (0 : ℝ)..b, P t) = (b : ℝ)^(α.val+1)/(α.val+1) := by
  have hα : -1 < α.val := α.property
  let P : ℝ → ℝ := fun t ↦ if 0 < t then t^α.val else 0
  have he (t : ℝ) (ht : 0 < t) : P t = t^α.val := by simp only [P, ite_eq_left ht]
  refine ⟨P,he,fun b ↦ ?_⟩
  have hb : (0 : ℝ) ≤ (b : ℝ) := b.coe_nonneg
  refine ⟨?_,?_⟩
  · erw [intervalIntegrable_iff_integrableOn_Ioo_of_le (f := P) (μ := volume) hb]
    apply (integrableOn_iff_comap_subtypeVal (f := P) (μ := volume) measurableSet_Ioo).mpr
    have hi := integrable_rpow_openInterval α 0 b
    erw [NNReal.coe_zero, min_eq_left hb, max_eq_right hb] at hi
    apply hi.congr
    filter_upwards [] with t
    exact (he t.val t.property.1).symm
  · erw [intervalIntegral.integral_of_le (f := P) (μ := volume) hb, integral_Ioc_eq_integral_Ioo,
      ← integral_subtype_comap measurableSet_Ioo P]
    have hi := integral_rpow_openInterval α 0 b
    erw [NNReal.coe_zero, min_eq_left hb, max_eq_right hb] at hi
    simp only [zero_le, ite_true, one_mul,
      zero_rpow (by linarith [hα] : α.val+1 ≠ 0), sub_zero] at hi
    calc
      _ = ∫ t : Ioo (0 : ℝ) b, t.val^α.val ∂Measure.comap Subtype.val volume := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact he t.val t.property.1
      _ = _ := hi
theorem integrable_powerLawLeft_kernel_and_integral (α : Ioi (-1 : ℝ)) (x : Ici (-1 : ℝ)) :
    Integrable (fun y : Ioo (-1 : ℝ) x.val ↦ (x.val-y.val)^α.val)
      (Measure.comap Subtype.val volume) ∧
    (∫ y : Ioo (-1 : ℝ) x.val, (x.val-y.val)^α.val ∂Measure.comap Subtype.val volume) =
      (x.val+1)^(α.val+1)/(α.val+1) := by
  obtain ⟨P,he,hP⟩ := positive_power_data α
  have hx : -1 ≤ x.val := x.property
  let b : ℝ≥0 := NNReal.mk (x.val+1) (by linarith)
  have hi : IntervalIntegrable (fun y ↦ P (x.val-y)) volume (-1) x.val := by
    convert ((hP b).1.symm.comp_sub_left x.val) using 1 <;> norm_num [b]
  have hj := (integrableOn_iff_comap_subtypeVal (f := fun y ↦ P (x.val-y)) measurableSet_Ioo).mp
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le x.property).mp hi)
  refine ⟨?_,?_⟩
  · apply hj.congr
    filter_upwards [] with y
    exact he (x.val-y.val) (sub_pos.mpr y.property.2)
  · calc
      _ = ∫ y : Ioo (-1 : ℝ) x.val, P (x.val-y.val) ∂Measure.comap Subtype.val volume := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact (he (x.val-y.val) (sub_pos.mpr y.property.2)).symm
      _ = ∫ y in (-1 : ℝ)..x.val, P (x.val-y) := by
        rw [integral_subtype_comap measurableSet_Ioo (fun y ↦ P (x.val-y)),
          intervalIntegral.integral_of_le x.property, integral_Ioc_eq_integral_Ioo]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left]
        convert (hP b).2 using 1 <;> try simp only [sub_self,sub_neg_eq_add]
        all_goals rfl
theorem integrable_powerLawRight_kernel_and_integral (α : Ioi (-1 : ℝ)) (x : Iic (1 : ℝ)) :
    Integrable (fun y : Ioo x.val (1 : ℝ) ↦ (y.val-x.val)^α.val)
      (Measure.comap Subtype.val volume) ∧
    (∫ y : Ioo x.val (1 : ℝ), (y.val-x.val)^α.val ∂Measure.comap Subtype.val volume) =
      (1-x.val)^(α.val+1)/(α.val+1) := by
  obtain ⟨P,he,hP⟩ := positive_power_data α
  have hx : x.val ≤ 1 := x.property
  let b : ℝ≥0 := NNReal.mk (1-x.val) (by linarith)
  have hi : IntervalIntegrable (fun y ↦ P (y-x.val)) volume x.val 1 := by
    convert (hP b).1.comp_sub_right x.val using 1 <;> norm_num [b]
  have hj := (integrableOn_iff_comap_subtypeVal (f := fun y ↦ P (y-x.val)) measurableSet_Ioo).mp
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le x.property).mp hi)
  refine ⟨?_,?_⟩
  · apply hj.congr
    filter_upwards [] with y
    exact he (y.val-x.val) (sub_pos.mpr y.property.1)
  · calc
      _ = ∫ y : Ioo x.val (1 : ℝ), P (y.val-x.val) ∂Measure.comap Subtype.val volume := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact (he (y.val-x.val) (sub_pos.mpr y.property.1)).symm
      _ = ∫ y in x.val..(1 : ℝ), P (y-x.val) := by
        rw [integral_subtype_comap measurableSet_Ioo (fun y ↦ P (y-x.val)),
          intervalIntegral.integral_of_le x.property, integral_Ioc_eq_integral_Ioo]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right]
        convert (hP b).2 using 1 <;> try simp only [sub_self]
        all_goals rfl
theorem integrable_powerLaw_kernel (α : Ioi (-1 : ℝ)) (x : Icc (-1 : ℝ) 1) :
    Integrable (fun y : PowerLawDomain x.val ↦ |x.val-y.val|^α.val)
      (Measure.comap Subtype.val volume) := by
  let K : ℝ → ℝ := fun y ↦ if y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x.val then
    |x.val-y|^α.val else 0
  have hl : IntegrableOn K (Ioo (-1 : ℝ) x.val) volume := by
    apply (integrableOn_iff_comap_subtypeVal (f := K) (μ := volume) measurableSet_Ioo).mpr
    apply (integrable_powerLawLeft_kernel_and_integral α ⟨x.val,x.property.1⟩).1.congr
    filter_upwards [] with y
    have hd : y.val ∈ Ioo (-1 : ℝ) 1 ∧ y.val ≠ x.val :=
      ⟨⟨y.property.1,y.property.2.trans_le x.property.2⟩,y.property.2.ne⟩
    simp only [Function.comp_def,K, ite_eq_left hd, abs_of_pos (sub_pos.mpr y.property.2)]
  have hr : IntegrableOn K (Ioo x.val (1 : ℝ)) volume := by
    apply (integrableOn_iff_comap_subtypeVal (f := K) (μ := volume) measurableSet_Ioo).mpr
    apply (integrable_powerLawRight_kernel_and_integral α ⟨x.val,x.property.2⟩).1.congr
    filter_upwards [] with y
    have hd : y.val ∈ Ioo (-1 : ℝ) 1 ∧ y.val ≠ x.val :=
      ⟨⟨x.property.1.trans_lt y.property.1,y.property.2⟩,y.property.1.ne'⟩
    simp only [Function.comp_def,K, ite_eq_left hd, abs_of_neg (sub_neg.mpr y.property.1),neg_sub]
  have hs : {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x.val} =
      Ioo (-1 : ℝ) x.val ∪ Ioo x.val (1 : ℝ) := by
    ext y
    constructor
    · rintro ⟨hy,hn⟩
      rcases lt_or_gt_of_ne hn with h | h
      · exact Or.inl ⟨hy.1,h⟩
      · exact Or.inr ⟨h,hy.2⟩
    · rintro (hy | hy)
      · exact ⟨⟨hy.1,hy.2.trans_le x.property.2⟩,hy.2.ne⟩
      · exact ⟨⟨x.property.1.trans_lt hy.1,hy.2⟩,hy.1.ne'⟩
  have hu := hl.union hr
  rw [← hs] at hu
  have hi := (integrableOn_iff_comap_subtypeVal (f := K) (μ := volume)
    (measurableSet_powerLawDomain x.val)).mp hu
  apply hi.congr
  filter_upwards [] with y
  change (if y.val ∈ Ioo (-1 : ℝ) 1 ∧ y.val ≠ x.val then _ else _) = _
  exact ite_eq_left y.property

/-- Constant inputs belong to every locally integrable power-law domain. -/
def PowerLawInput.one (α : Ioi (-1 : ℝ)) (x : Icc (-1 : ℝ) 1) : PowerLawInput α.val x.val :=
  ⟨fun _ ↦ 1, by simpa only [mul_one] using integrable_powerLaw_kernel α x⟩
def PowerLawLeftInput.one (α : Ioi (-1 : ℝ)) (x : Ici (-1 : ℝ)) : PowerLawLeftInput α.val x :=
  ⟨fun _ ↦ 1, by simpa only [mul_one] using (integrable_powerLawLeft_kernel_and_integral α x).1⟩
def PowerLawRightInput.one (α : Ioi (-1 : ℝ)) (x : Iic (1 : ℝ)) : PowerLawRightInput α.val x :=
  ⟨fun _ ↦ 1, by simpa only [mul_one] using (integrable_powerLawRight_kernel_and_integral α x).1⟩
theorem powerLawLeft_one (α : Ioi (-1 : ℝ)) (x : Ici (-1 : ℝ)) :
    powerLawLeft (.one α x) = (x.val+1)^(α.val+1)/(α.val+1) := by
  simpa only [powerLawLeft,PowerLawLeftInput.one,mul_one] using
    (integrable_powerLawLeft_kernel_and_integral α x).2
theorem powerLawRight_one (α : Ioi (-1 : ℝ)) (x : Iic (1 : ℝ)) :
    powerLawRight (.one α x) = (1-x.val)^(α.val+1)/(α.val+1) := by
  simpa only [powerLawRight,PowerLawRightInput.one,mul_one] using
    (integrable_powerLawRight_kernel_and_integral α x).2
end Real
namespace Real
/-- Continuous inputs on the closed interval give integrable weighted inputs. -/
def PowerLawInput.ofContinuous (α : Ioi (-1 : ℝ)) (x : Icc (-1 : ℝ) 1)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) : PowerLawInput α.val x.val := by
  refine ⟨fun y ↦ f ⟨y.val, Ioo_subset_Icc_self y.property.1⟩, ?_⟩
  have hc : Continuous (fun y : PowerLawDomain x.val ↦
      f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩) := by fun_prop
  exact (integrable_powerLaw_kernel α x).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y ↦ ContinuousMap.norm_coe_le_norm f _))

/-- The continuous constructor agrees pointwise on the kernel domain. -/
theorem PowerLawInput.ofContinuous_apply (α : Ioi (-1 : ℝ)) (x : Icc (-1 : ℝ) 1)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) (y : PowerLawDomain x.val) :
    (PowerLawInput.ofContinuous α x f).val y = f ⟨y.val, Ioo_subset_Icc_self y.property.1⟩ := rfl
end Real
namespace Real
/-- A certified weighted input has an integrable ambient representative of the
whole integrand. The proof extends it by zero only outside its typed domain. -/
theorem PowerLawInput.exists_weightedIntervalRepresentative {α x : ℝ} (f : PowerLawInput α x) :
    ∃ F : ℝ → ℝ, (∀ y : PowerLawDomain x, F y.val = |x-y.val|^α*f.val y) ∧
      IntervalIntegrable F volume (-1) 1 ∧
      powerLawIntegral f = ∫ y in (-1 : ℝ)..1, F y := by
  let F : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x then
    |x-y|^α*f.val ⟨y,h⟩ else 0
  have he (y : PowerLawDomain x) : F y.val = |x-y.val|^α*f.val y := by
    simp only [F, dite_eq_left y.property]
  have hs : {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x} =ᵐ[volume] Ioo (-1 : ℝ) 1 := by
    filter_upwards [volume.ae_ne x] with y hy
    exact propext ⟨And.left, fun h ↦ ⟨h,hy⟩⟩
  have hi : IntegrableOn F {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x} volume := by
    apply (integrableOn_iff_comap_subtypeVal (f := F) (μ := volume) (measurableSet_powerLawDomain x)).mpr
    change Integrable (fun y : PowerLawDomain x ↦ F y.val) _
    convert f.property using 1
    funext y
    exact he y
    all_goals rfl
  refine ⟨F, he, ?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mpr
      ((integrableOn_congr_set_ae hs).mp hi)
  · unfold powerLawIntegral
    simp_rw [← he]
    erw [integral_subtype_comap (μ := volume) (measurableSet_powerLawDomain x) F,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_set hs
end Real
namespace Real
/-- Left restriction of a full integrable input. -/
def PowerLawInput.left {α : ℝ} (x : Icc (-1 : ℝ) 1) (f : PowerLawInput α x.val) :
    PowerLawLeftInput α ⟨x.val, x.property.1⟩ := by
  let e (y : Ioo (-1 : ℝ) x.val) : PowerLawDomain x.val :=
    ⟨y.val,⟨y.property.1,y.property.2.trans_le x.property.2⟩,y.property.2.ne⟩
  refine ⟨fun y ↦ f.val (e y), ?_⟩
  obtain ⟨F,he,hF,_⟩ := PowerLawInput.exists_weightedIntervalRepresentative f
  have hl : IntervalIntegrable F volume (-1) x.val := hF.mono_set (by
    rw [uIcc_of_le x.property.1, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl x.property.2)
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le x.property.1).mp hl
  have hj := (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hi
  apply hj.congr
  filter_upwards [] with y
  change F ((e y).val) = (x.val-y.val)^α*f.val (e y)
  rw [he]
  dsimp only [e]
  rw [abs_of_pos (sub_pos.mpr y.property.2)]
/-- Right restriction of a full integrable input. -/
def PowerLawInput.right {α : ℝ} (x : Icc (-1 : ℝ) 1) (f : PowerLawInput α x.val) :
    PowerLawRightInput α ⟨x.val, x.property.2⟩ := by
  let e (y : Ioo x.val (1 : ℝ)) : PowerLawDomain x.val :=
    ⟨y.val,⟨x.property.1.trans_lt y.property.1,y.property.2⟩,y.property.1.ne'⟩
  refine ⟨fun y ↦ f.val (e y), ?_⟩
  obtain ⟨F,he,hF,_⟩ := PowerLawInput.exists_weightedIntervalRepresentative f
  have hr : IntervalIntegrable F volume x.val 1 := hF.mono_set (by
    rw [uIcc_of_le x.property.2, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc x.property.1 le_rfl)
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le x.property.2).mp hr
  have hj := (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hi
  apply hj.congr
  filter_upwards [] with y
  change F ((e y).val) = (y.val-x.val)^α*f.val (e y)
  rw [he]
  dsimp only [e]
  rw [abs_of_neg (sub_neg.mpr y.property.1), neg_sub]
end Real
namespace Real
/-- Decomposition on the entire weighted-integrability domain. -/
theorem powerLawIntegral_eq_left_add_right {α : ℝ} (x : Icc (-1 : ℝ) 1)
    (f : PowerLawInput α x.val) :
    powerLawIntegral f = powerLawLeft (f.left x) + powerLawRight (f.right x) := by
  obtain ⟨F,he,hF,hv⟩ := PowerLawInput.exists_weightedIntervalRepresentative f
  have hl : IntervalIntegrable F volume (-1) x.val := hF.mono_set (by
    rw [uIcc_of_le x.property.1, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl x.property.2)
  have hr : IntervalIntegrable F volume x.val 1 := hF.mono_set (by
    rw [uIcc_of_le x.property.2, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc x.property.1 le_rfl)
  have hL : powerLawLeft (PowerLawInput.left x f) = ∫ y in (-1 : ℝ)..x.val, F y := by
    calc
      _ = ∫ y : Ioo (-1 : ℝ) x.val, F y ∂Measure.comap Subtype.val volume := by
        apply integral_congr_ae
        filter_upwards [] with y
        let z : PowerLawDomain x.val :=
          ⟨y.val,⟨y.property.1,y.property.2.trans_le x.property.2⟩,y.property.2.ne⟩
        change (x.val-y.val)^α*f.val z = F z.val
        rw [he]
        dsimp only [z]
        rw [abs_of_pos (sub_pos.mpr y.property.2)]
      _ = _ := by rw [integral_subtype_comap measurableSet_Ioo F,
        intervalIntegral.integral_of_le x.property.1, integral_Ioc_eq_integral_Ioo]
  have hR : powerLawRight (PowerLawInput.right x f) = ∫ y in x.val..(1 : ℝ), F y := by
    calc
      _ = ∫ y : Ioo x.val (1 : ℝ), F y ∂Measure.comap Subtype.val volume := by
        apply integral_congr_ae
        filter_upwards [] with y
        let z : PowerLawDomain x.val :=
          ⟨y.val,⟨x.property.1.trans_lt y.property.1,y.property.2⟩,y.property.1.ne'⟩
        change (y.val-x.val)^α*f.val z = F z.val
        rw [he]
        dsimp only [z]
        rw [abs_of_neg (sub_neg.mpr y.property.1), neg_sub]
      _ = _ := by rw [integral_subtype_comap measurableSet_Ioo F,
        intervalIntegral.integral_of_le x.property.2, integral_Ioc_eq_integral_Ioo]
  rw [hv,hL,hR]
  exact (intervalIntegral.integral_add_adjacent_intervals hl hr).symm
theorem powerLawIntegral_one (α : Ioi (-1 : ℝ)) (x : Icc (-1 : ℝ) 1) :
    powerLawIntegral (.one α x) =
      ((x.val+1)^(α.val+1)+(1-x.val)^(α.val+1))/(α.val+1) := by
  rw [powerLawIntegral_eq_left_add_right x]
  have hl : (PowerLawInput.one α x).left x =
      PowerLawLeftInput.one α ⟨x.val,x.property.1⟩ := Subtype.ext rfl
  have hr : (PowerLawInput.one α x).right x =
      PowerLawRightInput.one α ⟨x.val,x.property.2⟩ := Subtype.ext rfl
  rw [hl,hr,powerLawLeft_one,powerLawRight_one,add_div]
end Real
namespace Real
/-- Reflection preserves the full weighted-integrability domain. -/
def PowerLawInput.reflect {α x : ℝ} (f : PowerLawInput α x) : PowerLawInput α (-x) := by
  let e (y : PowerLawDomain (-x)) : PowerLawDomain x :=
    ⟨-y.val, ⟨by constructor <;> linarith [y.property.1.1,y.property.1.2],
      fun h ↦ y.property.2 (by linarith)⟩⟩
  refine ⟨fun y ↦ f.val (e y), ?_⟩
  obtain ⟨F,he,hF,_⟩ := PowerLawInput.exists_weightedIntervalRepresentative f
  have hg : IntervalIntegrable (fun y ↦ F (-y)) volume (-1) 1 := by
    simpa only [neg_neg] using ((IntervalIntegrable.iff_comp_neg).mp hF).symm
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp hg
  have hj := hi.mono_set (show {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ -x} ⊆ Ioo (-1 : ℝ) 1 from fun _ h ↦ h.1)
  have hk := (integrableOn_iff_comap_subtypeVal (measurableSet_powerLawDomain (-x))).mp hj
  apply hk.congr
  filter_upwards [] with y
  change F ((e y).val) = |-x-y.val|^α*f.val (e y)
  rw [he]
  have ha : |x-(e y).val| = |-x-y.val| := by
    change |x-(-y.val)| = |-x-y.val|
    rw [show -x-y.val = -(x-(-y.val)) by ring, abs_neg]
  exact congrArg (fun k : ℝ ↦ k^α*f.val (e y)) ha
/-- Reflection changes only the input and the evaluation point. -/
theorem powerLawIntegral_neg {α x : ℝ} (f : PowerLawInput α x) :
    powerLawIntegral f.reflect = powerLawIntegral f := by
  obtain ⟨F,he,hF,hv⟩ := PowerLawInput.exists_weightedIntervalRepresentative f
  obtain ⟨G,hg,hG,hgv⟩ := PowerLawInput.exists_weightedIntervalRepresentative (PowerLawInput.reflect f)
  rw [hgv,hv]
  calc
    _ = ∫ y in (-1 : ℝ)..1, F (-y) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo,
        (volume.ae_ne (-x)).filter_mono (ae_mono Measure.restrict_le_self)] with y hy hn
      have hd : y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ -x := ⟨hy,hn⟩
      rw [hg ⟨y,hd⟩]
      let z : PowerLawDomain x := ⟨-y, ⟨by constructor <;> linarith [hy.1,hy.2],
        fun h ↦ hn (by linarith)⟩⟩
      change |-x-y|^α*f.val z = F z.val
      rw [he]
      have ha : |-x-y| = |x-z.val| := by
        change |-x-y| = |x-(-y)|
        rw [show -x-y = -(x-(-y)) by ring, abs_neg]
      exact congrArg (fun k : ℝ ↦ k^α*f.val z) ha
    _ = _ := by
      rw [intervalIntegral.integral_comp_neg]
      norm_num
end Real
namespace Real
/-- Left input characterization and positive kernel base. -/
theorem powerLawLeft_spec {α : ℝ} {x : Ici (-1 : ℝ)} (f : PowerLawLeftInput α x) :
    (∀ y : Ioo (-1 : ℝ) x.val, 0 < x.val-y.val) ∧
    Integrable (fun y : Ioo (-1 : ℝ) x.val ↦ (x.val-y.val)^α*f.val y)
      (Measure.comap Subtype.val volume) ∧
    powerLawLeft f = ∫ y : Ioo (-1 : ℝ) x.val,
      (x.val-y.val)^α*f.val y ∂Measure.comap Subtype.val volume :=
  ⟨fun y ↦ sub_pos.mpr y.property.2, f.property, rfl⟩
/-- Right input characterization and positive kernel base. -/
theorem powerLawRight_spec {α : ℝ} {x : Iic (1 : ℝ)} (f : PowerLawRightInput α x) :
    (∀ y : Ioo x.val (1 : ℝ), 0 < y.val-x.val) ∧
    Integrable (fun y : Ioo x.val (1 : ℝ) ↦ (y.val-x.val)^α*f.val y)
      (Measure.comap Subtype.val volume) ∧
    powerLawRight f = ∫ y : Ioo x.val (1 : ℝ),
      (y.val-x.val)^α*f.val y ∂Measure.comap Subtype.val volume :=
  ⟨fun y ↦ sub_pos.mpr y.property.1, f.property, rfl⟩
end Real

namespace Real
/-- Removing one point preserves an integrable function and its integral on the open interval. -/
theorem integrable_integral_powerLawDomain (x : ℝ)
    (f : {f : Ioo (-1 : ℝ) 1 → ℝ // Integrable f (Measure.comap Subtype.val volume)}) :
    Integrable (fun y : PowerLawDomain x ↦ f.val ⟨y.val,y.property.1⟩)
      (Measure.comap Subtype.val volume) ∧
    (∫ y : PowerLawDomain x, f.val ⟨y.val,y.property.1⟩ ∂Measure.comap Subtype.val volume) =
      ∫ y : Ioo (-1 : ℝ) 1, f.val y ∂Measure.comap Subtype.val volume := by
  let F : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo (-1 : ℝ) 1 then f.val ⟨y,h⟩ else 0
  have he (y : Ioo (-1 : ℝ) 1) : F y.val = f.val y := by
    simp only [F,dite_eq_left y.property]
  have hI : IntegrableOn F (Ioo (-1 : ℝ) 1) volume := by
    apply (integrableOn_iff_comap_subtypeVal (f := F) (μ := volume) measurableSet_Ioo).mpr
    apply f.property.congr
    filter_upwards [] with y
    exact (he y).symm
  have hD := hI.mono_set (show {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x} ⊆ Ioo (-1 : ℝ) 1 from fun _ h ↦ h.1)
  have hJ := (integrableOn_iff_comap_subtypeVal (f := F) (μ := volume)
    (measurableSet_powerLawDomain x)).mp hD
  refine ⟨?_,?_⟩
  · apply hJ.congr
    filter_upwards [] with y
    exact he ⟨y.val,y.property.1⟩
  · calc
      _ = ∫ y : PowerLawDomain x, F y.val ∂Measure.comap Subtype.val volume := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact (he ⟨y.val,y.property.1⟩).symm
      _ = ∫ y in {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x}, F y := by
        erw [integral_subtype_comap (μ := volume) (measurableSet_powerLawDomain x) F]
      _ = ∫ y in Ioo (-1 : ℝ) 1, F y := by
        apply setIntegral_congr_set
        filter_upwards [volume.ae_ne x] with y hy
        exact propext ⟨And.left,fun h ↦ ⟨h,hy⟩⟩
      _ = ∫ y : Ioo (-1 : ℝ) 1, F y.val ∂Measure.comap Subtype.val volume := by
        rw [integral_subtype_comap measurableSet_Ioo F]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact he y


end Real
