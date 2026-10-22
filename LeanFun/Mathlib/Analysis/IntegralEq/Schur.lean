/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-! # L² operators from dominated kernel marginals

The Schur construction factors through the L² space of the kernel measure.
It uses measure domination and Hilbert adjoints rather than pointwise choices
of L² representatives. Reference: the classical Schur test.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Pullback to a joint measure when the corresponding marginal is dominated. -/
def dominatedL2Pullback (μ : Measure X) (ν : Measure Y) (f : Y → X)
    (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞) (h : ν.map f ≤ C • μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℝ f ⟨hf, rfl⟩).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul hC h)

/-- The pullback acts by composition almost everywhere. -/
theorem dominatedL2Pullback_ae (μ : Measure X) (ν : Measure Y) (f : Y → X)
    (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞) (h : ν.map f ≤ C • μ)
    (u : Lp ℝ 2 μ) : dominatedL2Pullback μ ν f hf hC h u =ᵐ[ν] u ∘ f := by
  apply (Lp.coeFn_compMeasurePreserving _ (show MeasurePreserving f ν (ν.map f) from ⟨hf,rfl⟩)).trans
  exact ae_of_ae_map hf.aemeasurable (Lp.coeFn_LpToLpOfMeasureLeSMul hC h u)

/-- The pullback norm is bounded by the square root of the marginal bound. -/
theorem norm_dominatedL2Pullback_le (μ : Measure X) (ν : Measure Y) (f : Y → X)
    (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞) (h : ν.map f ≤ C • μ) :
    ‖dominatedL2Pullback μ ν f hf hC h‖ ≤ Real.sqrt C.toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  change ‖Lp.compMeasurePreserving f ⟨hf,rfl⟩ (Lp.LpToLpOfMeasureLeSMul hC h u)‖ ≤ _
  rw [Lp.norm_compMeasurePreserving]
  have hb := (Lp.LpToLpOfMeasureLeSMul hC h : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (ν.map f)).le_opNorm u
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa [Real.sqrt_eq_rpow] using
    (Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := 2) hC h)

/-- A joint measure with bounded marginals defines a bounded operator between L² spaces. -/
def schurL2Operator (μ : Measure X) (ν : Measure Y) (κ : Measure (X × Y))
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ) (hsnd : κ.map Prod.snd ≤ D • ν) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (dominatedL2Pullback μ κ Prod.fst measurable_fst hC hfst).adjoint.comp
    (dominatedL2Pullback ν κ Prod.snd measurable_snd hD hsnd)

/-- The Schur norm bound is the geometric mean of the two marginal bounds. -/
theorem norm_schurL2Operator_le (μ : Measure X) (ν : Measure Y) (κ : Measure (X × Y))
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ) (hsnd : κ.map Prod.snd ≤ D • ν) :
    ‖schurL2Operator μ ν κ hC hD hfst hsnd‖ ≤ Real.sqrt C.toReal * Real.sqrt D.toReal := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul (norm_dominatedL2Pullback_le μ κ _ measurable_fst hC hfst)
    (norm_dominatedL2Pullback_le ν κ _ measurable_snd hD hsnd) (norm_nonneg _)
    (Real.sqrt_nonneg _)

/-- The operator is characterized by integration against its joint kernel measure. -/
theorem inner_schurL2Operator (μ : Measure X) (ν : Measure Y) (κ : Measure (X × Y))
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ) (hsnd : κ.map Prod.snd ≤ D • ν)
    (u : Lp ℝ 2 ν) (v : Lp ℝ 2 μ) :
    ⟪v, schurL2Operator μ ν κ hC hD hfst hsnd u⟫_ℝ =
      ∫ z, v z.1 * u z.2 ∂κ := by
  rw [schurL2Operator, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [dominatedL2Pullback_ae μ κ _ measurable_fst hC hfst v,
    dominatedL2Pullback_ae ν κ _ measurable_snd hD hsnd u] with z hz hz'
  simp only [hz,hz',Function.comp_apply, Real.inner_apply]

/-- The joint pairing is absolutely integrable for all L² inputs. -/
theorem integrable_schurL2_pair (μ : Measure X) (ν : Measure Y) (κ : Measure (X × Y))
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ) (hsnd : κ.map Prod.snd ≤ D • ν)
    (u : Lp ℝ 2 ν) (v : Lp ℝ 2 μ) :
    Integrable (fun z ↦ v z.1*u z.2) κ := by
  apply (L2.integrable_inner (𝕜 := ℝ)
    (dominatedL2Pullback μ κ Prod.fst measurable_fst hC hfst v)
    (dominatedL2Pullback ν κ Prod.snd measurable_snd hD hsnd u)).congr
  filter_upwards [dominatedL2Pullback_ae μ κ _ measurable_fst hC hfst v,
    dominatedL2Pullback_ae ν κ _ measurable_snd hD hsnd u] with z hz hz'
  simp only [hz,hz',Function.comp_apply,Real.inner_apply]

/-- First marginal of a nonnegative kernel measure. -/
theorem map_fst_withDensity_prod (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (k : X × Y → ℝ≥0∞) (hk : Measurable k) :
    ((μ.prod ν).withDensity k).map Prod.fst =
      μ.withDensity (fun x ↦ ∫⁻ y, k (x,y) ∂ν) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ measurable_fst,
    lintegral_withDensity_eq_lintegral_mul (μ.prod ν) hk (by fun_prop : Measurable (fun z : X × Y ↦ φ z.1)),
    lintegral_prod _ (hk.mul (by fun_prop : Measurable (fun z : X × Y ↦ φ z.1))).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hφ]
  apply lintegral_congr
  intro x
  simpa only [Pi.mul_apply] using lintegral_mul_const (φ x)
    (show Measurable (fun y ↦ k (x,y)) from hk.comp measurable_prodMk_left)

/-- Second marginal of a nonnegative kernel measure. -/
theorem map_snd_withDensity_prod (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (k : X × Y → ℝ≥0∞) (hk : Measurable k) :
    ((μ.prod ν).withDensity k).map Prod.snd =
      ν.withDensity (fun y ↦ ∫⁻ x, k (x,y) ∂μ) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ measurable_snd,
    lintegral_withDensity_eq_lintegral_mul (μ.prod ν) hk (by fun_prop : Measurable (fun z : X × Y ↦ φ z.2)),
    lintegral_prod_symm _ (hk.mul (by fun_prop : Measurable (fun z : X × Y ↦ φ z.2))).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hφ]
  apply lintegral_congr
  intro x
  simpa only [Pi.mul_apply] using lintegral_mul_const (φ x)
    (show Measurable (fun y ↦ k (y,x)) from hk.comp measurable_prodMk_right)

end MeasureTheory
