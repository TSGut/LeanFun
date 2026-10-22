/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Duffy
import Mathlib.Topology.Algebra.MvPolynomial

import Mathlib.Topology.Algebra.Polynomial

/-! # The standard triangle weight from product coordinates
The transported measure agrees, up to the explicitly stated mass factor, with
the triangular weighted integral in DLMF 18.37.8.
-/

public section
open MeasureTheory Polynomial Set
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- Polynomial integrals have the standard triangular weight and the explicit affine mass. -/
theorem integral_proriolProductMeasure_density {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (p : MvPolynomial (Fin 2) ℝ) :
    ∫ v, eval v p ∂proriolProductMeasure α β γ =
      (2 : ℝ)^(α+2*β+2*γ+3) *
        ∫ x : Ioo (0 : ℝ) 1, (1-(x : ℝ))^α *
          ∫ y : Ioo (0 : ℝ) (x : ℝ), ((x : ℝ)-(y : ℝ))^β * (y : ℝ)^γ *
            eval (![(x : ℝ),(y : ℝ)] : Fin 2 → ℝ) p := by
  let μ := unitJacobiMeasure α (β+γ+1)
  let ν := unitJacobiMeasure β γ
  let := isFiniteMeasure_unitJacobiMeasure hα (show -1 < β+γ+1 by linarith)
  let := isFiniteMeasure_unitJacobiMeasure hβ hγ
  have hm : Integrable (fun v ↦ eval v p) (proriolProductMeasure α β γ) := by
    simpa only [proriolProductMeasure, map_one, mul_one] using
      (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul p 1
  have ht := koornwinderMeasure_integral_univ (fun x ↦ x) continuous_id μ ν
    ⟨fun v ↦ eval v p, hm⟩
  have hi := ht.1
  have hc : Continuous (fun v : ℝ × ℝ ↦ eval (![v.1,v.1*v.2] : Fin 2 → ℝ) p) := by
    exact p.continuous_eval.comp (by fun_prop)
  have hf : Measurable (fun x ↦ ∫ z, eval (![x,x*z] : Fin 2 → ℝ) p ∂ν) :=
    hc.stronglyMeasurable.integral_prod_right'.measurable
  have hzi (x : ℝ) : Integrable (fun z ↦ eval (![x,x*z] : Fin 2 → ℝ) p) ν := by
    have hzcont : Continuous (fun z : ℝ ↦ eval (![x,x*z] : Fin 2 → ℝ) p) :=
      p.continuous_eval.comp (by fun_prop)
    rw [show ν = unitJacobiMeasure β γ from rfl, unitJacobiMeasure,
      integrable_map_measure hzcont.aestronglyMeasurable (by fun_prop)]
    exact integrable_jacobiMeasure hβ hγ (p.continuous_eval.comp (by fun_prop)).continuousOn
  have hin (x : ℝ) := integral_unitJacobiMeasure_subtype β γ
    ⟨(fun z ↦ eval (![x,x*z] : Fin 2 → ℝ) p), hzi x⟩
    ((p.continuous_eval.comp (by fun_prop)).measurable)
  rw [proriolProductMeasure, ht.2, integral_prod _ hi]
  change (∫ x, (∫ z, eval (![x,x*z] : Fin 2 → ℝ) p ∂ν) ∂μ) = _
  rw [integral_unitJacobiMeasure_subtype _ _ ⟨_,hi.integral_prod_left⟩ hf]
  simp only
  simp_rw [unitJacobiWeight_apply]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hin x]
  simp only
  simp_rw [unitJacobiWeight_apply, mul_assoc]
  rw [integral_const_mul]
  have hzint := integrable_unitJacobiMeasure_density_input β γ
    ⟨(fun z ↦ eval (![(x : ℝ),(x : ℝ)*z] : Fin 2 → ℝ) p),hzi x⟩
  have hd := integral_duffy_jacobi β γ x.property.1
    ⟨(fun y ↦ eval (![(x : ℝ),y] : Fin 2 → ℝ) p),hzint⟩
  simp only [mul_assoc] at hd
  rw [← hd]
  have htwo : (2 : ℝ)^(α+(β+γ+1)+1) * (2 : ℝ)^(β+γ+1) =
      (2 : ℝ)^(α+2*β+2*γ+3) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [← htwo]
  ring

end MvPolynomial
