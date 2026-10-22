/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.Schur
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalDensity
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
/-! # The reflected Volterra triangle and the shifted Jacobi measure

The two marginals of simplex area are (1-x) dx on [0,1]. Scaling area by
four gives exactly the shifted (1,0) Jacobi measure in both coordinates.
Reference: Gutleb's thesis, §§2.3 and 2.7.
-/

open MeasureTheory Set
open scoped ENNReal
@[expose] public noncomputable section
namespace Real
local notation "ν" => volume.restrict (Icc (0 : ℝ) 1)
/-- Area measure on the reflected Volterra simplex in the unit square. -/
def reflectedVolterraTriangleMeasure : Measure (ℝ × ℝ) :=
  ((ν).prod ν).restrict {z | z.1 + z.2 ≤ 1}
instance : IsFiniteMeasure reflectedVolterraTriangleMeasure := by
  unfold reflectedVolterraTriangleMeasure
  infer_instance
/-- The first marginal of simplex area has density 1-x. -/
theorem map_fst_reflectedVolterraTriangleMeasure :
    reflectedVolterraTriangleMeasure.map Prod.fst = (ν).withDensity (fun x ↦ ENNReal.ofReal (1-x)) := by
  ext s hs
  rw [reflectedVolterraTriangleMeasure, Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (measurable_fst hs),
    Measure.prod_apply ((measurable_fst hs).inter (measurableSet_le (show Measurable (fun z : ℝ × ℝ ↦ z.1 + z.2) from measurable_fst.add measurable_snd) measurable_const)),
    withDensity_apply _ hs, ← lintegral_indicator (μ := ν) hs (fun x : ℝ ↦ ENNReal.ofReal (1-x))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  by_cases hxs : x ∈ s
  · have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' s ∩ {z : ℝ × ℝ | z.1 + z.2 ≤ 1}) = Iic (1-x) := by
      ext y; simp [hxs, le_sub_iff_add_le, add_comm]
    rw [he, Measure.restrict_apply measurableSet_Iic]
    have hi : Iic (1-x) ∩ Icc (0 : ℝ) 1 = Icc 0 (1-x) := by
      ext y; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor <;> intro h
      · exact ⟨h.2.1,h.1⟩
      · exact ⟨h.2,h.1,h.2.trans (by linarith [hx.1])⟩
    rw [hi, Real.volume_Icc]
    simp [hxs]
  · have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' s ∩ {z : ℝ × ℝ | z.1 + z.2 ≤ 1}) = ∅ := by
      ext y; simp [hxs]
    simp [he,hxs]
/-- The second marginal has the same density by reflection symmetry. -/
theorem map_snd_reflectedVolterraTriangleMeasure :
    reflectedVolterraTriangleMeasure.map Prod.snd = (ν).withDensity (fun y ↦ ENNReal.ofReal (1-y)) := by
  ext s hs
  rw [reflectedVolterraTriangleMeasure, Measure.map_apply measurable_snd hs,
    Measure.restrict_apply (measurable_snd hs),
    Measure.prod_apply_symm ((measurable_snd hs).inter (measurableSet_le (show Measurable (fun z : ℝ × ℝ ↦ z.1 + z.2) from measurable_fst.add measurable_snd) measurable_const)),
    withDensity_apply _ hs, ← lintegral_indicator (μ := ν) hs (fun x : ℝ ↦ ENNReal.ofReal (1-x))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  by_cases hys : y ∈ s
  · have he : (fun x : ℝ ↦ (x,y)) ⁻¹' (Prod.snd ⁻¹' s ∩ {z : ℝ × ℝ | z.1 + z.2 ≤ 1}) = Iic (1-y) := by
      ext x; simp [hys, le_sub_iff_add_le]
    rw [he, Measure.restrict_apply measurableSet_Iic]
    have hi : Iic (1-y) ∩ Icc (0 : ℝ) 1 = Icc 0 (1-y) := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor <;> intro h
      · exact ⟨h.2.1,h.1⟩
      · exact ⟨h.2,h.1,h.2.trans (by linarith [hy.1])⟩
    rw [hi, Real.volume_Icc]
    simp [hys]
  · have he : (fun x : ℝ ↦ (x,y)) ⁻¹' (Prod.snd ⁻¹' s ∩ {z : ℝ × ℝ | z.1 + z.2 ≤ 1}) = ∅ := by
      ext x; simp [hys]
    simp [he,hys]
end Real
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial
/-- The raw shifted Jacobi measure is four times either simplex marginal. -/
theorem unitJacobiMeasure_one_zero_triangle : unitJacobiMeasure 1 0 =
    (4 : ℝ≥0∞) • Real.reflectedVolterraTriangleMeasure.map Prod.fst := by
  let := isFiniteMeasure_unitJacobiMeasure (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0)
  let : IsFiniteMeasure ((4 : ℝ≥0∞) • Real.reflectedVolterraTriangleMeasure.map Prod.fst) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)⟩
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : IntegrableInput (unitJacobiMeasure 1 0) := ⟨f, by
      rw [unitJacobiMeasure, integrable_map_measure f.continuous.aestronglyMeasurable (by fun_prop)]
      exact integrable_jacobiMeasure (by norm_num) (by norm_num)
        (f.continuous.comp (by fun_prop)).continuousOn⟩
  have hg : Measurable g.val := by dsimp [g]; fun_prop
  have hd : (∫ x, g.val x ∂unitJacobiMeasure 1 0) = 4 *
      ∫ x in (0 : ℝ)..1, (1-x) * g.val x := by
    rw [integral_unitJacobiMeasure_subtype 1 0 g hg]
    simp only [unitJacobiWeight_apply, add_zero, Real.rpow_one, Real.rpow_zero,
      mul_one, mul_assoc]
    norm_num only [one_add_one_eq_two, Real.rpow_two]
    rw [integral_const_mul, integral_subtype measurableSet_Ioo (fun x : ℝ ↦ (1-x)*g.val x),
      restrict_Ioo_eq_restrict_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  dsimp only [g] at hd
  rw [hd,
    integral_smul_measure, Real.map_fst_reflectedVolterraTriangleMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun x ↦ ENNReal.ofReal_lt_top))]
  norm_num only [add_zero, one_add_one_eq_two, Real.rpow_one, Real.rpow_zero,
    mul_one, ENNReal.toReal_ofNat, smul_eq_mul, Real.rpow_natCast]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    restrict_Ioc_eq_restrict_Icc]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hx.2)]
end Polynomial

namespace Real
/-- Scaled simplex area with both marginals equal to the shifted Jacobi measure. -/
def jacobiVolterraJoint : Measure (ℝ × ℝ) := (4 : ℝ≥0∞) • reflectedVolterraTriangleMeasure
instance : IsFiniteMeasure jacobiVolterraJoint := by
  unfold jacobiVolterraJoint
  constructor
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)
/-- The first scaled marginal is the shifted (1,0) Jacobi measure. -/
theorem map_fst_jacobiVolterraJoint :
    jacobiVolterraJoint.map Prod.fst = Polynomial.unitJacobiMeasure 1 0 := by
  rw [jacobiVolterraJoint, Measure.map_smul _ measurable_fst.aemeasurable]
  exact Polynomial.unitJacobiMeasure_one_zero_triangle.symm
/-- The second scaled marginal is the shifted (1,0) Jacobi measure. -/
theorem map_snd_jacobiVolterraJoint :
    jacobiVolterraJoint.map Prod.snd = Polynomial.unitJacobiMeasure 1 0 := by
  rw [jacobiVolterraJoint, Measure.map_smul _ measurable_snd.aemeasurable, map_snd_reflectedVolterraTriangleMeasure,
    ← map_fst_reflectedVolterraTriangleMeasure]
  exact Polynomial.unitJacobiMeasure_one_zero_triangle.symm
/-- The joint measure is supported on the reflected unit simplex. -/
theorem ae_mem_jacobiVolterraJoint :
    ∀ᵐ z ∂jacobiVolterraJoint, z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc 0 1 ∧ z.1+z.2 ≤ 1 := by
  have hx : ∀ᵐ z ∂jacobiVolterraJoint, z.1 ∈ Icc (0 : ℝ) 1 :=
    ae_of_ae_map measurable_fst.aemeasurable (by
      rw [map_fst_jacobiVolterraJoint]
      exact Polynomial.ae_mem_Icc_unitJacobiMeasure 1 0)
  have hy : ∀ᵐ z ∂jacobiVolterraJoint, z.2 ∈ Icc (0 : ℝ) 1 :=
    ae_of_ae_map measurable_snd.aemeasurable (by
      rw [map_snd_jacobiVolterraJoint]
      exact Polynomial.ae_mem_Icc_unitJacobiMeasure 1 0)
  have ht : ∀ᵐ z ∂jacobiVolterraJoint, z.1+z.2 ≤ 1 :=
    Measure.ae_smul_measure (ae_restrict_mem
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)) _
  filter_upwards [hx,hy,ht] with z hx hy ht
  exact ⟨hx,hy,ht⟩
end Real
namespace Real
/-- Integration over the scaled reflected triangle by its vertical sections. -/
theorem integral_jacobiVolterraJoint (f : ℝ × ℝ → ℝ)
    (hf : Integrable f jacobiVolterraJoint) :
    (∫ z, f z ∂jacobiVolterraJoint) =
      4 * ∫ s in Icc (0 : ℝ) 1, ∫ y in (0 : ℝ)..(1-s), f (s,y) := by
  let T : Set (ℝ × ℝ) := {z | z.1 + z.2 ≤ 1}
  have hT : MeasurableSet T :=
    measurableSet_le (show Measurable (fun z : ℝ × ℝ ↦ z.1 + z.2) from
      measurable_fst.add measurable_snd) measurable_const
  have hi : Integrable (T.indicator f)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [integrable_indicator_iff hT]
    exact (integrable_smul_measure (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp hf
  rw [jacobiVolterraJoint, integral_smul_measure]
  norm_num only [ENNReal.toReal_ofNat, smul_eq_mul]
  congr 1
  rw [reflectedVolterraTriangleMeasure, ← integral_indicator hT, integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have he : (fun y ↦ T.indicator f (s,y)) = (Iic (1-s)).indicator (fun y ↦ f (s,y)) := by
    funext y
    have h : s+y ≤ 1 ↔ y ≤ 1-s := by constructor <;> intro h <;> linarith
    simp only [Set.indicator_apply, T, mem_ofPred_eq, mem_Iic, h]
  rw [he, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have he : Iic (1-s) ∩ Icc (0 : ℝ) 1 = Icc 0 (1-s) := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · intro h; exact ⟨h.2.1,h.1⟩
    · intro h; exact ⟨h.2,h.1,by linarith [hs.1]⟩
  rw [he, intervalIntegral.integral_of_le (by linarith [hs.2]), restrict_Ioc_eq_restrict_Icc]
end Real
namespace Polynomial
/-- Integrable Jacobi inputs have an integrable classical weighted integrand. -/
theorem integrable_unitJacobiMeasure_one_zero
    (f : IntegrableInput (unitJacobiMeasure 1 0)) :
    IntegrableOn (fun x : ℝ ↦ (1-x)*f.val x) (Icc (0 : ℝ) 1) := by
  have h := integrable_unitJacobiMeasure_density_input 1 0 f
  simp only [Real.rpow_one, Real.rpow_zero, mul_one] at h
  have hi : IntegrableOn (fun x : ℝ ↦ (1-x)*f.val x) (Ioo (0 : ℝ) 1) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).2 h
  simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Icc] using hi

/-- Integration against the shifted (1,0) Jacobi measure, including its mass factor. -/
theorem integral_unitJacobiMeasure_one_zero
    (f : IntegrableInput (unitJacobiMeasure 1 0)) :
    (∫ x, f.val x ∂unitJacobiMeasure 1 0) =
      4 * ∫ x in Icc (0 : ℝ) 1, (1-x)*f.val x := by
  rcases f with ⟨f, hf⟩
  change (∫ x, f x ∂unitJacobiMeasure 1 0) = 4 * ∫ x in Icc (0 : ℝ) 1, (1-x)*f x
  rw [unitJacobiMeasure_one_zero_triangle, Real.map_fst_reflectedVolterraTriangleMeasure,
    integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun x ↦ ENNReal.ofReal_lt_top))]
  norm_num only [ENNReal.toReal_ofNat, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hx.2)]
end Polynomial
