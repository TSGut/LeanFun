/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitInterval
import Mathlib.Tactic.FieldSimp

/-! # Radial powers for affine Jacobi measures
Reference: the outer parameter shift in DLMF 18.37.7–8.
-/

public section
open MeasureTheory Set
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

private theorem jacobiWeight_beta_add_nat (α β : ℝ) (k : ℕ) (x : Ioo (-1 : ℝ) 1) :
    (jacobiWeight α (β+k) x : ℝ) = (1+(x : ℝ))^k * (jacobiWeight α β x : ℝ) := by
  change (1-(x : ℝ))^α * (1+(x : ℝ))^(β+k) = _
  rw [Real.rpow_add (by linarith [x.property.1] : 0 < 1+(x : ℝ)),Real.rpow_natCast]
  change _ = (1+(x : ℝ))^k * ((1-(x : ℝ))^α * (1+(x : ℝ))^β)
  ring
/-- Radial powers preserve every convergent measurable input in the shifted measure. -/
theorem integral_pow_unitJacobiMeasure_integrable (α β : ℝ) (k : ℕ)
    (f : IntegrableInput (unitJacobiMeasure α (β + k))) (hf : Measurable f.val) :
    Integrable (fun x ↦ x ^ k * f.val x) (unitJacobiMeasure α β) ∧
      (∫ x, x ^ k * f.val x ∂unitJacobiMeasure α β) =
        ((2 : ℝ) ^ k)⁻¹ * ∫ x, f.val x ∂unitJacobiMeasure α (β + k) := by
  rcases f with ⟨f,hfint⟩
  simp only at *
  have hi : Integrable (fun x ↦ x^k*f x) (unitJacobiMeasure α β) := by
    rw [unitJacobiMeasure, integrable_map_measure (by fun_prop) (by fun_prop),
      integrable_jacobiMeasure_iff]
    have h := hfint
    rw [unitJacobiMeasure, integrable_map_measure hf.aestronglyMeasurable (by fun_prop),
      integrable_jacobiMeasure_iff] at h
    convert h.const_mul ((2 : ℝ)^k)⁻¹ using 1
    ext x
    rw [jacobiWeight_beta_add_nat]
    change _ * (((x+1)/2)^k*f ((x+1)/2)) = _
    rw [div_pow]
    dsimp only [Function.comp_def]
    ring
  refine ⟨hi, ?_⟩
  have hx : Integrable (fun t : ℝ ↦ ((t+1)/2)^k*f ((t+1)/2)) (jacobiMeasure α β) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).mp hi
  have hy : Integrable (fun t : ℝ ↦ f ((t+1)/2)) (jacobiMeasure α (β+k)) :=
    (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).mp hfint
  rw [integral_unitJacobiMeasure α β ⟨_,hi⟩,integral_unitJacobiMeasure α (β+k) ⟨f,hfint⟩,
    integral_jacobiMeasure α β ⟨_,hx⟩,integral_jacobiMeasure α (β+k) ⟨_,hy⟩,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [jacobiWeight_beta_add_nat]
  rw [div_pow]
  ring

end Polynomial
