/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Classical weighted integration on an open interval

Weights have their domain in the point type. Integrable inputs carry their
integrability, so integration never selects the nonintegrable default.
Reference: the weighted orthogonality measures of DLMF Section 18.2.
-/

@[expose] public noncomputable section
open Set
open scoped NNReal ENNReal
namespace MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace

/-- Real integrable functions, retaining pointwise representatives (DLMF 18.2). -/
abbrev IntegrableInput {X : Type*} [MeasurableSpace X] (μ : Measure X) :=
  {f : X → ℝ // Integrable f μ}

/-- A bundled input has a genuine finite integral. -/
theorem IntegrableInput.integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : IntegrableInput μ) : Integrable f.val μ := f.property

/-- A continuous nonnegative density on an open interval, pushed to the real line.
Reference: DLMF 18.2(i). -/
def openIntervalWeightMeasure (a b : ℝ) (w : C(Ioo a b, ℝ≥0)) : Measure ℝ :=
  Measure.map Subtype.val (volume.withDensity fun x : Ioo a b ↦ (w x : ℝ≥0∞))

/-- Integrability is exactly integrability of the weighted subtype function. -/
theorem integrable_openIntervalWeightMeasure_iff (a b : ℝ) (w : C(Ioo a b, ℝ≥0))
    (f : ℝ → ℝ) :
    Integrable f (openIntervalWeightMeasure a b w) ↔
      Integrable (fun x : Ioo a b ↦ (w x : ℝ) * f x) volume := by
  rw [openIntervalWeightMeasure,
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo).integrable_map_iff,
    integrable_withDensity_iff_integrable_coe_smul w.continuous.measurable]
  rfl

/-- The integral formula, with a domain that excludes nonintegrable inputs. -/
theorem integral_openIntervalWeightMeasure (a b : ℝ) (w : C(Ioo a b, ℝ≥0))
    (f : IntegrableInput (openIntervalWeightMeasure a b w)) :
    ∫ x, f.val x ∂openIntervalWeightMeasure a b w =
      ∫ x : Ioo a b, (w x : ℝ) * f.val x := by
  change (∫ x, f.val x ∂Measure.map Subtype.val
    (volume.withDensity fun x : Ioo a b ↦ (w x : ℝ≥0∞))) = _
  rw [
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo).integral_map,
    integral_withDensity_eq_integral_smul w.continuous.measurable]
  rfl

/-- Internal transport bridge to a globally represented density. -/
theorem openIntervalWeightMeasure_eq (a b : ℝ) (w : C(Ioo a b, ℝ≥0))
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) (hw : ∀ x : Ioo a b, (w x : ℝ≥0∞) = g x) :
    openIntervalWeightMeasure a b w = (volume.restrict (Ioo a b)).withDensity g := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [openIntervalWeightMeasure,
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo).lintegral_map,
    lintegral_withDensity_eq_lintegral_mul _ w.continuous.measurable.coe_nnreal_ennreal
      (show Measurable (fun x : Ioo a b ↦ φ (x : ℝ)) from hφ.comp measurable_subtype_coe),
    lintegral_withDensity_eq_lintegral_mul _ hg hφ]
  simp_rw [hw]
  exact lintegral_subtype_comap (s := Ioo a b) measurableSet_Ioo (fun x ↦ g x * φ x)

/-- A continuous nonnegative density gives an s-finite measure on its open domain. -/
theorem sFinite_openIntervalWeightMeasure (a b : ℝ) (w : C(Ioo a b, ℝ≥0)) :
    SFinite (openIntervalWeightMeasure a b w) := by
  let g : ℝ → ℝ≥0∞ := Function.extend Subtype.val (fun t : Ioo a b ↦ (w t : ℝ≥0∞)) (fun _ ↦ 0)
  have hg : Measurable g :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo).measurable_extend
      (ENNReal.continuous_coe.measurable.comp w.continuous.measurable) measurable_const
  have he := openIntervalWeightMeasure_eq a b w g hg (fun t ↦
    (Subtype.val_injective.extend_apply (fun t : Ioo a b ↦ (w t : ℝ≥0∞)) (fun _ : ℝ ↦ 0) t).symm)
  rw [he]
  infer_instance
/-- A continuous density with respect to Lebesgue measure has no atoms. -/
theorem nullSingletonClass_openIntervalWeightMeasure (a b : ℝ) (w : C(Ioo a b, ℝ≥0)) :
    NullSingletonClass (openIntervalWeightMeasure a b w) := by
  let g : ℝ → ℝ≥0∞ := Function.extend Subtype.val (fun t : Ioo a b ↦ (w t : ℝ≥0∞)) (fun _ ↦ 0)
  have hg : Measurable g :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo).measurable_extend
      (ENNReal.continuous_coe.measurable.comp w.continuous.measurable) measurable_const
  have he := openIntervalWeightMeasure_eq a b w g hg (fun t ↦
    (Subtype.val_injective.extend_apply (fun t : Ioo a b ↦ (w t : ℝ≥0∞)) (fun _ : ℝ ↦ 0) t).symm)
  rw [he]
  infer_instance

end MeasureTheory
