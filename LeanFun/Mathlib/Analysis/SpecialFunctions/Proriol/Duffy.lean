/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalDensity

/-! # Weighted Duffy substitution on a triangle
The radial Jacobian converts the two Jacobi weights to the triangle weight in
DLMF 18.37.8. The weighted input is integrable on the open unit interval.
-/

public section
open MeasureTheory Set
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- The inner affine scaling accounts for the radial power and its Jacobian. -/
theorem integral_duffy_jacobi (β γ : ℝ) {x : ℝ} (hx : 0 < x)
    (f : {f : ℝ → ℝ // Integrable (fun z : Ioo (0 : ℝ) 1 ↦
      (1-(z : ℝ))^β * (z : ℝ)^γ * f (x*z)) volume}) :
    x^(β+γ+1) * (∫ z : Ioo (0 : ℝ) 1, (1-(z : ℝ))^β * (z : ℝ)^γ * f.val (x*z)) =
      ∫ y : Ioo (0 : ℝ) x, (x-(y : ℝ))^β * (y : ℝ)^γ * f.val y := by
  let W : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo (0 : ℝ) x then
    (x-y)^β * y^γ * f.val y else 0
  have he := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) W x
  simp only [smul_eq_mul, mul_zero, mul_one] at he
  have hw : (∫ y : Ioo (0 : ℝ) x, (x-(y : ℝ))^β * (y : ℝ)^γ * f.val y) =
      ∫ y in (0 : ℝ)..x, W y := by
    have hwe (y : Ioo (0 : ℝ) x) : W y = (x-(y : ℝ))^β * (y : ℝ)^γ * f.val y := by
      simp only [W, dite_eq_left y.property]
    simp_rw [← hwe]
    rw [integral_subtype measurableSet_Ioo W, restrict_Ioo_eq_restrict_Ioc,
      intervalIntegral.integral_of_le hx.le]
  rw [hw, ← he, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← restrict_Ioo_eq_restrict_Ioc, ← integral_subtype measurableSet_Ioo,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : x*(z : ℝ) ∈ Ioo (0 : ℝ) x :=
    ⟨mul_pos hx z.property.1, by nlinarith [z.property.2]⟩
  simp only [W, dite_eq_left hz]
  rw [show x-x*(z : ℝ)=x*(1-z) by ring,
    Real.mul_rpow hx.le (by linarith [z.property.2]),
    Real.mul_rpow hx.le z.property.1.le,
    Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one]
  ring

end Polynomial
