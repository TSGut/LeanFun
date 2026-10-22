/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.JacobiVolterraMeasure
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
@[expose] public noncomputable section
/-! # Local integrability in the shifted (1,0) Jacobi space

The weighted and ordinary interval measures have the same null sets. Away
from the vanishing endpoint weight, weighted L² functions are locally L¹.
This supplies the local uniqueness hypotheses for first-kind Volterra equations.
-/

open MeasureTheory Set
open scoped ENNReal
namespace Polynomial
local notation "μ" => unitJacobiMeasure 1 0
local notation "ν" => volume.restrict (Icc (0 : ℝ) 1)
/-- The Jacobi weight changes no null sets on the unit interval. -/
theorem ae_unitJacobiMeasure_one_zero_iff {p : ℝ → Prop} :
    (∀ᵐ x ∂μ, p x) ↔ ∀ᵐ x ∂ν, p x := by
  rw [unitJacobiMeasure_one_zero_triangle, Real.map_fst_reflectedVolterraTriangleMeasure,
    Measure.ae_ennreal_smul_measure_iff (by norm_num : (4 : ℝ≥0∞) ≠ 0),
    ae_withDensity_iff (by fun_prop)]
  have hp : ∀ᵐ x ∂ν, ENNReal.ofReal (1-x) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ((ν).ae_ne 1)] with x hx hx1
    exact (ENNReal.ofReal_pos.mpr (by rcases hx with ⟨_,hx⟩; have : x < 1 := lt_of_le_of_ne hx hx1; linarith)).ne'
  constructor
  · intro h
    filter_upwards [h,hp] with x hx hp
    exact hx hp
  · intro h
    filter_upwards [h] with x hx
    exact fun _ ↦ hx
/-- A weighted L² input is Lebesgue integrable on every interval ending below one. -/
theorem integrableOn_coe_jacobiOneZeroLp (f : Lp ℝ 2 μ) {c : ℝ} (hc : c < 1) :
    IntegrableOn (fun x ↦ f x) (Icc 0 c) := by
  let := isFiniteMeasure_unitJacobiMeasure (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0)
  have hi := (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  conv at hi =>
    arg 2
    rw [unitJacobiMeasure_one_zero_triangle, Real.map_fst_reflectedVolterraTriangleMeasure]
  rw [integrable_smul_measure (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ∞),
    integrable_withDensity_iff (by fun_prop)
      (Filter.Eventually.of_forall (fun x ↦ ENNReal.ofReal_lt_top))] at hi
  have hw : Integrable (fun x ↦ f x * (1-x)) ν := hi.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hx.2)])
  have hr : IntegrableOn (fun x ↦ f x*(1-x)) (Icc 0 c) := by
    have hh := hw.integrableOn (s := Icc 0 c)
    rwa [IntegrableOn, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (Icc_subset_Icc le_rfl hc.le)] at hh
  have hd : ContinuousOn (fun x : ℝ ↦ (1-x)⁻¹) (Icc 0 c) :=
    (continuous_const.sub continuous_id).continuousOn.inv₀ (fun x hx ↦ by change (1 : ℝ)-x ≠ 0; linarith [hx.2])
  apply (hr.mul_continuousOn hd isCompact_Icc).congr_fun _ measurableSet_Icc
  intro x hx
  dsimp only
  rw [mul_assoc, mul_inv_cancel₀ (show (1 : ℝ)-x ≠ 0 by linarith [hx.2]), mul_one]
end Polynomial
