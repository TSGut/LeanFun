/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitInterval

/-! # Lebesgue density of the affine Jacobi measure
Reference: affine change of variables in DLMF Table 18.3.1.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- The Jacobian and weight constants for the affine Jacobi substitution. -/
theorem two_mul_jacobiWeight_affine (α β : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    2 * ((1 - ((2*x-1) : ℝ)) ^ (α) * (1 + ((2*x-1) : ℝ)) ^ (β)) =
      (2 : ℝ) ^ (α+β+1) * ((1-x) ^ α * x ^ β) := by
  rw [show 1-(2*x-1) = 2*(1-x) by ring, show 1+(2*x-1)=2*x by ring,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith [hx.2]),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hx.1),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

/-- The affine Jacobi density, including its mass-preserving factor. -/
def unitJacobiWeight (α β : ℝ) : C(Ioo (0 : ℝ) 1, ℝ≥0) where
  toFun x := 2 * jacobiWeight α β
    ⟨2 * (x : ℝ) - 1, by constructor <;> linarith [x.property.1, x.property.2]⟩
  continuous_toFun := by
    apply continuous_const.mul
    apply (jacobiWeight α β).continuous.comp
    apply Continuous.subtype_mk
    fun_prop

/-- The affine density formula has positive bases at every typed point. -/
theorem unitJacobiWeight_apply (α β : ℝ) (x : Ioo (0 : ℝ) 1) :
    (unitJacobiWeight α β x : ℝ) =
      (2 : ℝ) ^ (α + β + 1) * ((1 - (x : ℝ)) ^ α * (x : ℝ) ^ β) :=
  two_mul_jacobiWeight_affine α β x.property

private theorem integral_unitJacobiMeasure_subtype_data (a b : ℝ) (f : IntegrableInput (unitJacobiMeasure a b)) :
    Integrable (fun x : Ioo (0 : ℝ) 1 ↦ (unitJacobiWeight a b x : ℝ)*f.val x) volume ∧
      (∫ x, f.val x ∂unitJacobiMeasure a b) =
        ∫ x : Ioo (0 : ℝ) 1, (unitJacobiWeight a b x : ℝ)*f.val x := by
  rcases f with ⟨f,hf⟩
  have hp : Integrable (fun t : ℝ ↦ f ((t+1)/2)) (jacobiMeasure a b) :=
    (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).mp hf
  have ht := (integrable_jacobiMeasure_iff a b _).mp hp
  let W : ℝ → ℝ := fun t ↦ if h : t ∈ Ioo (-1 : ℝ) 1 then
    (jacobiWeight a b ⟨t,h⟩ : ℝ)*f ((t+1)/2) else 0
  have hi : IntervalIntegrable W volume (-1 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mpr
    convert ht using 1
    ext x
    simp only [W, Function.comp_def, dite_eq_left x.property]
  have hc := ((hi.comp_sub_right 1).comp_mul_left (c := 2)).const_mul 2
  norm_num only at hc
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hc
  have he (x : Ioo (0 : ℝ) 1) : 2*W (2*(x : ℝ)-1) =
      (unitJacobiWeight a b x : ℝ)*f x := by
    have hx : 2*(x : ℝ)-1 ∈ Ioo (-1 : ℝ) 1 := by
      constructor <;> linarith [x.property.1,x.property.2]
    simp only [W, dite_eq_left hx]
    rw [show (2*(x : ℝ)-1+1)/2 = x by ring]
    change _ = (2*(jacobiWeight a b ⟨2*(x : ℝ)-1,hx⟩ : ℝ))*f x
    ring
  refine ⟨hc.congr (Filter.Eventually.of_forall he), ?_⟩
  have hj : (∫ x, f x ∂unitJacobiMeasure a b) =
      ∫ t : Ioo (-1 : ℝ) 1, (jacobiWeight a b t : ℝ)*f (((t : ℝ)+1)/2) := by
    rw [unitJacobiMeasure, integral_map (by fun_prop) hf.aestronglyMeasurable]
    exact integral_jacobiMeasure a b ⟨_,hp⟩
  rw [hj]
  have hW : (∫ t : Ioo (-1 : ℝ) 1, (jacobiWeight a b t : ℝ)*f (((t : ℝ)+1)/2)) =
      ∫ t in (-1 : ℝ)..1, W t := by
    have heq (t : Ioo (-1 : ℝ) 1) : W t =
      (jacobiWeight a b t : ℝ)*f (((t : ℝ)+1)/2) := by
      simp only [W, dite_eq_left t.property]
    simp_rw [← heq]
    rw [integral_subtype measurableSet_Ioo W,restrict_Ioo_eq_restrict_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [hW]
  have hs := intervalIntegral.smul_integral_comp_mul_sub
    (a := (0 : ℝ)) (b := 1) W 2 1
  norm_num only [smul_eq_mul,mul_zero,zero_sub,mul_one] at hs
  rw [← hs, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← restrict_Ioo_eq_restrict_Ioc, ← integral_subtype measurableSet_Ioo
      (fun t : ℝ ↦ 2*W (2*t-1))]
  exact integral_congr_ae (Filter.Eventually.of_forall he)

/-- A measurable integrable input has an integrable subtype density product. -/
theorem integrable_unitJacobiWeight_mul (α β : ℝ)
    (f : IntegrableInput (unitJacobiMeasure α β)) (hf : Measurable f.val) :
    Integrable (fun x : Ioo (0 : ℝ) 1 ↦ (unitJacobiWeight α β x : ℝ) * f.val x) volume := by
  have _ := hf
  exact (integral_unitJacobiMeasure_subtype_data α β f).1

/-- The classical affine density formula, with integrability of both sides. -/
theorem integral_unitJacobiMeasure_subtype (α β : ℝ)
    (f : IntegrableInput (unitJacobiMeasure α β)) (hf : Measurable f.val) :
    ∫ x, f.val x ∂unitJacobiMeasure α β =
      ∫ x : Ioo (0 : ℝ) 1, (unitJacobiWeight α β x : ℝ) * f.val x := by
  have _ := hf
  exact (integral_unitJacobiMeasure_subtype_data α β f).2

/-- Internal affine integrability transport, including integrable endpoint singularities. -/
theorem integrable_unitJacobiMeasure_density_input (a b : ℝ)
    (f : IntegrableInput (unitJacobiMeasure a b)) :
    Integrable (fun x : Ioo (0 : ℝ) 1 =>
      (1-(x : ℝ))^a * (x : ℝ)^b * f.val x) volume := by
  have h := (integral_unitJacobiMeasure_subtype_data a b f).1.const_mul
    (((2 : ℝ)^(a+b+1))⁻¹)
  convert h using 1
  ext x
  rw [unitJacobiWeight_apply]
  field_simp
end Polynomial
