/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Measure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Radial density of the Cartesian disk measure

The separated measure integrates continuous functions against the usual disk
weight `(1-x²-y²)^β`, with no normalization constant.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, disk families.
-/

public section
open MeasureTheory Set Polynomial
open scoped NNReal ENNReal
namespace MvPolynomial

private theorem symmetricWeight (β x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ((1 - (x : ℝ)) ^ (β) * (1 + (x : ℝ)) ^ (β)) = (1 - x ^ 2) ^ β := by
  rw [← Real.mul_rpow (by linarith [hx.2] : 0 ≤ 1 - x)
    (by linarith [hx.1] : 0 ≤ 1 + x)]
  congr 1
  ring

/-- The disk Jacobian identity for domain-typed Jacobi weights. -/
theorem diskCoordinates_weight (β : ℝ) (x z : Ioo (-1 : ℝ) 1) :
    (jacobiWeight (β + 1 / 2) (β + 1 / 2) x : ℝ) * (jacobiWeight β β z : ℝ) =
      Real.sqrt (1 - (x : ℝ) ^ 2) *
        (1 - (x : ℝ) ^ 2 - (Real.sqrt (1 - (x : ℝ) ^ 2) * (z : ℝ)) ^ 2) ^ β := by
  have hx0 : 0 < 1 - (x : ℝ)^2 := by nlinarith [x.property.1,x.property.2]
  have hz0 : 0 ≤ 1 - (z : ℝ)^2 := by nlinarith [z.property.1,z.property.2]
  change ((1-(x : ℝ))^(β+1/2)*(1+(x : ℝ))^(β+1/2)) *
    ((1-(z : ℝ))^β*(1+(z : ℝ))^β) = _
  rw [symmetricWeight _ _ x.property, symmetricWeight _ _ z.property]
  rw [show 1-(x : ℝ)^2-(Real.sqrt (1-(x : ℝ)^2)*(z : ℝ))^2 =
      (1-(x : ℝ)^2)*(1-(z : ℝ)^2) by rw [mul_pow, Real.sq_sqrt hx0.le]; ring,
    Real.mul_rpow hx0.le hz0, Real.rpow_add hx0, Real.sqrt_eq_rpow]
  ring


attribute [local instance] Measure.Subtype.measureSpace

theorem integrable_diskSlice {β : ℝ} (hβ : -1 < β) (x : Ioo (-1 : ℝ) 1)
    {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    Integrable (fun y : Ioo (-Real.sqrt (1-(x : ℝ)^2)) (Real.sqrt (1-(x : ℝ)^2)) ↦
      (1-(x : ℝ)^2-(y : ℝ)^2)^β * f ![(x : ℝ),(y : ℝ)]) volume := by
  let r := Real.sqrt (1-(x : ℝ)^2)
  have hA : 0 < 1-(x : ℝ)^2 := by nlinarith [x.property.1,x.property.2]
  have hr : 0 < r := Real.sqrt_pos.2 hA
  have hr2 : r^2 = 1-(x : ℝ)^2 := Real.sq_sqrt hA.le
  let W : ℝ → ℝ := fun z ↦ if hz : z ∈ Ioo (-1 : ℝ) 1 then
    (jacobiWeight β β ⟨z,hz⟩ : ℝ) * f ![(x : ℝ),r*z] else 0
  have hw : Integrable (fun z : Ioo (-1 : ℝ) 1 ↦ W z) volume := by
    have ht := (integrable_jacobiMeasure_iff β β _).mp
      (integrable_jacobiMeasure hβ hβ
        (show ContinuousOn (fun z : ℝ ↦ f ![(x : ℝ),r*z]) (Icc (-1 : ℝ) 1) from
          (hf.comp (by fun_prop)).continuousOn))
    simpa only [W, dite_eq_left (Subtype.property _)] using ht
  have hi : IntervalIntegrable W volume (-1 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mpr hw
  have hj := hi.comp_mul_left (c := r⁻¹)
  simp only [div_inv_eq_mul, neg_mul, one_mul] at hj
  have hk := hj.const_mul ((1-(x : ℝ)^2)^β)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : -r ≤ r),
    integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hk
  apply hk.congr
  filter_upwards [] with y
  have hz : r⁻¹*(y : ℝ) ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [inv_pos.mpr hr, mul_inv_cancel₀ hr.ne',
      mul_lt_mul_of_pos_left y.property.1 (inv_pos.mpr hr),
      mul_lt_mul_of_pos_left y.property.2 (inv_pos.mpr hr)]
  have he : 1-(x : ℝ)^2-(y : ℝ)^2 =
      (1-(x : ℝ)^2)*((1-r⁻¹*(y : ℝ))*(1+r⁻¹*(y : ℝ))) := by
    rw [← hr2]
    field_simp
    ring
  dsimp only [Function.comp_def]
  rw [show W (r⁻¹*(y : ℝ)) =
    (jacobiWeight β β ⟨r⁻¹*(y : ℝ),hz⟩ : ℝ) * f ![(x : ℝ),r*(r⁻¹*(y : ℝ))] by
      simp only [W, dite_eq_left hz]]
  rw [show r * (r⁻¹ * (y : ℝ)) = y by field_simp]
  rw [he, Real.mul_rpow hA.le (mul_nonneg (by linarith [hz.2]) (by linarith [hz.1])),
    Real.mul_rpow (by linarith [hz.2]) (by linarith [hz.1])]
  change (1-(x : ℝ)^2)^β *
    (((1-r⁻¹*(y : ℝ))^β * (1+r⁻¹*(y : ℝ))^β) * f ![(x : ℝ),(y : ℝ)]) = _
  ring

 theorem diskSlice_radical_pos (x : Ioo (-1 : ℝ) 1)
    (y : Ioo (-Real.sqrt (1-(x : ℝ)^2)) (Real.sqrt (1-(x : ℝ)^2))) :
    0 < 1-(x : ℝ)^2-(y : ℝ)^2 := by
  have hA : 0 < 1-(x : ℝ)^2 := by nlinarith [x.property.1,x.property.2]
  have hr := Real.sqrt_pos.2 hA
  have hr2 := Real.sq_sqrt hA.le
  nlinarith [y.property.1,y.property.2]

/-- The classical weighted integrand on a vertical open disk slice.
Reference: Dunkl–Xu, disk measures and Cartesian coordinates. -/
noncomputable def diskSliceInput (β : Ioi (-1 : ℝ))
    (f : C((Fin 2 → ℝ), ℝ)) (x : Ioo (-1 : ℝ) 1) :
    IntegrableInput (volume : Measure (Ioo (-Real.sqrt (1-(x : ℝ)^2))
      (Real.sqrt (1-(x : ℝ)^2)))) :=
  ⟨fun y ↦ (1-(x : ℝ)^2-(y : ℝ)^2)^(β : ℝ) * f ![(x : ℝ),(y : ℝ)], by
    exact integrable_diskSlice β.property x f.continuous⟩

 theorem diskSliceInput_integral (β : Ioi (-1 : ℝ))
    (f : C((Fin 2 → ℝ), ℝ)) (x : Ioo (-1 : ℝ) 1) :
    (∫ y, (diskSliceInput β f x).val y) =
      (jacobiWeight ((β : ℝ)+1/2) ((β : ℝ)+1/2) x : ℝ) *
        ∫ z, f ![(x : ℝ),Real.sqrt (1-(x : ℝ)^2)*z] ∂jacobiMeasure β β := by
  let r := Real.sqrt (1-(x : ℝ)^2)
  have hA : 0 < 1-(x : ℝ)^2 := by nlinarith [x.property.1,x.property.2]
  have hr : 0 < r := Real.sqrt_pos.2 hA
  let V : ℝ → ℝ := fun y ↦ if hy : y ∈ Ioo (-r) r then
    (1-(x : ℝ)^2-y^2)^(β : ℝ) * f ![(x : ℝ),y] else 0
  have hv (y : Ioo (-r) r) : V y =
      (1-(x : ℝ)^2-(y : ℝ)^2)^(β : ℝ)*f ![(x : ℝ),(y : ℝ)] := by
    simp only [V, dite_eq_left y.property]
  have hvint : (∫ y, (diskSliceInput β f x).val y) = ∫ y in -r..r, V y := by
    change (∫ y : Ioo (-r) r,
      (1-(x : ℝ)^2-(y : ℝ)^2)^(β : ℝ)*f ![(x : ℝ),(y : ℝ)]) = _
    simp_rw [← hv]
    rw [integral_subtype measurableSet_Ioo V, restrict_Ioo_eq_restrict_Ioc,
      intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have hrow : Integrable (fun z : ℝ ↦ f ![(x : ℝ),r*z]) (jacobiMeasure β β) :=
    integrable_jacobiMeasure β.property β.property
      (show ContinuousOn (fun z : ℝ ↦ f ![(x : ℝ),r*z]) (Icc (-1 : ℝ) 1) from
        (f.continuous.comp (by fun_prop)).continuousOn)
  rw [hvint, integral_jacobiMeasure (β : ℝ) β ⟨_,hrow⟩]
  have hs := intervalIntegral.smul_integral_comp_mul_left V
    (a := (-1 : ℝ)) (b := 1) r
  simp only [mul_neg, mul_one, smul_eq_mul] at hs
  rw [← hs, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← restrict_Ioo_eq_restrict_Ioc, ← integral_subtype measurableSet_Ioo (fun z : ℝ ↦ V (r*z)),
    ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : r*(z : ℝ) ∈ Ioo (-r) r := by
    constructor <;> nlinarith [z.property.1,z.property.2]
  simp only [V, dite_eq_left hz ]
  have hid := diskCoordinates_weight (β : ℝ) x z
  dsimp only [r] at *
  rw [← mul_assoc, ← hid, mul_assoc]

/-- Typed Fubini transport; each inner row is classically integrable. -/
theorem integrable_integral_dunklXuDiskMeasure_iterated (β : Ioi (-1 : ℝ)) (f : C((Fin 2 → ℝ), ℝ)) :
    Integrable (fun x : Ioo (-1 : ℝ) 1 ↦
      (jacobiWeight ((β : ℝ)+1/2) ((β : ℝ)+1/2) x : ℝ) *
        ∫ z, f ![(x : ℝ),Real.sqrt (1-(x : ℝ)^2)*z] ∂jacobiMeasure β β) volume ∧
    (∫ v, f v ∂dunklXuDiskMeasure β) =
      ∫ x : Ioo (-1 : ℝ) 1,
        (jacobiWeight ((β : ℝ)+1/2) ((β : ℝ)+1/2) x : ℝ) *
          ∫ z, f ![(x : ℝ),Real.sqrt (1-(x : ℝ)^2)*z] ∂jacobiMeasure β β := by
  let := isFiniteMeasure_jacobiMeasure β.property β.property
  have hα : -1 < (β : ℝ)+1/2 := by have h : -1 < (β : ℝ) := β.property; linarith
  let : IsFiniteMeasure (Measure.map (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ)
      (volume.withDensity fun x : Ioo (-1 : ℝ) 1 ↦
        (jacobiWeight ((β : ℝ)+1/2) ((β : ℝ)+1/2) x : ℝ≥0∞))) :=
    isFiniteMeasure_jacobiMeasure hα hα
  let : IsFiniteMeasure (volume.withDensity fun x : Ioo (-1 : ℝ) 1 ↦
      (jacobiWeight ((β : ℝ)+1/2) ((β : ℝ)+1/2) x : ℝ≥0∞)) :=
    Measure.isFiniteMeasure_of_map (f := (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ))
      measurable_subtype_coe.aemeasurable
  have hm : Measurable (fun v : Ioo (-1 : ℝ) 1 × ℝ ↦
      (![v.1, Real.sqrt (1-(v.1 : ℝ)^2)*v.2] : Fin 2 → ℝ)) := by fun_prop
  have hi := (integrable_map_measure f.continuous.aestronglyMeasurable
    hm.aemeasurable).mp (by simpa only [dunklXuDiskMeasure_eq_map_open] using
      (integrable_dunklXuDiskMeasure β.property f.continuous))
  have hrow (x : Ioo (-1 : ℝ) 1) :
      Integrable (fun z : ℝ ↦ f ![(x : ℝ),Real.sqrt (1-(x : ℝ)^2)*z])
        (jacobiMeasure β β) :=
    integrable_jacobiMeasure β.property β.property (show ContinuousOn (fun z : ℝ ↦ f ![(x : ℝ),Real.sqrt (1-(x : ℝ)^2)*z])
      (Icc (-1 : ℝ) 1) from (f.continuous.comp (by fun_prop)).continuousOn)
  have ho := hi.integral_prod_left
  rw [integrable_withDensity_iff_integrable_coe_smul
    (jacobiWeight ((β : ℝ)+1/2) ((β : ℝ)+1/2)).continuous.measurable] at ho
  refine ⟨ho, ?_⟩
  rw [integral_dunklXuDiskMeasure_open (β : ℝ)
    ⟨f, integrable_dunklXuDiskMeasure β.property f.continuous⟩]
  dsimp only [Subtype.coe_mk]
  erw [integral_prod _ hi, integral_withDensity_eq_integral_smul
      (jacobiWeight ((β : ℝ)+1/2) ((β : ℝ)+1/2)).continuous.measurable]
  rfl

/-- The integrable outer function formed from the classical vertical slices. -/
noncomputable def diskSlicesInput (β : Ioi (-1 : ℝ))
    (f : C((Fin 2 → ℝ), ℝ)) : IntegrableInput (volume : Measure (Ioo (-1 : ℝ) 1)) :=
  ⟨fun x ↦ ∫ y, (diskSliceInput β f x).val y, by
    apply (integrable_integral_dunklXuDiskMeasure_iterated β f).1.congr
    exact Filter.Eventually.of_forall (fun x ↦ (diskSliceInput_integral β f x).symm)⟩

 theorem integral_dunklXuDiskMeasure_eq_slices (β : Ioi (-1 : ℝ))
    (f : C((Fin 2 → ℝ), ℝ)) :
    (∫ v, f v ∂dunklXuDiskMeasure β) = ∫ x, (diskSlicesInput β f).val x := by
  rw [(integrable_integral_dunklXuDiskMeasure_iterated β f).2]
  change _ = ∫ x : Ioo (-1 : ℝ) 1, ∫ y, (diskSliceInput β f x).val y
  simp_rw [diskSliceInput_integral]

/-- Every slice input is integrable, including singular integrable disk weights. -/
theorem diskSliceInput_integrable (β : Ioi (-1 : ℝ))
    (f : C((Fin 2 → ℝ), ℝ)) (x : Ioo (-1 : ℝ) 1) :
    Integrable (diskSliceInput β f x).val volume := (diskSliceInput β f x).integrable

/-- The iterated slice integral has an integrable outer input. -/
theorem diskSlicesInput_integrable (β : Ioi (-1 : ℝ))
    (f : C((Fin 2 → ℝ), ℝ)) :
    Integrable (diskSlicesInput β f).val volume := (diskSlicesInput β f).integrable

end MvPolynomial
