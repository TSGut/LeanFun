/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Proof-level transport of nonnegative densities

A density on its nonnegative locus can be transported using a measurable zero
extension. The extension is an existential proof device, not a new density definition.
-/

public section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace MeasureTheory
/-- A measurable nonnegative density on its locus has a measurable zero extension,
whose weighted measure is exactly the pushforward of the restricted source. -/
theorem exists_nonnegativeDensity_extension {α : Type*} [MeasurableSpace α]
    (f : α → ℝ) (hf : Measurable f) :
    ∃ w : α → ℝ≥0, Measurable w ∧
      (∀ x (hx : 0 ≤ f x), w x = NNReal.mk (f x) hx) ∧
      (∀ x, ¬ 0 ≤ f x → w x = 0) ∧
      ∀ μ : Measure α,
        Measure.map Subtype.val ((μ.comap (Subtype.val : {x // 0 ≤ f x} → α)).withDensity
          (fun x => (NNReal.mk (f x.val) x.property : ℝ≥0∞))) =
          μ.withDensity (fun x => (w x : ℝ≥0∞)) := by
  let w (x : α) : ℝ≥0 := if h : 0 ≤ f x then NNReal.mk (f x) h else 0
  have hw : Measurable w := by
    apply measurable_coe_nnreal_real_iff.mp
    have he : (fun x => (w x : ℝ)) = Set.piecewise {x | 0 ≤ f x} f 0 := by
      funext x
      by_cases hx : 0 ≤ f x <;> simp [w, Set.piecewise, hx]
    rw [he]
    exact hf.piecewise (measurableSet_le measurable_const hf) measurable_const
  refine ⟨w, hw, (fun x hx => by simp [w, hx]), (fun x hx => by simp [w, hx]), ?_⟩
  intro μ
  have hs : MeasurableSet {x | 0 ≤ f x} := measurableSet_le measurable_const hf
  have he : Measure.map Subtype.val ((μ.comap (Subtype.val : {x // 0 ≤ f x} → α)).withDensity
      (fun x => (NNReal.mk (f x.val) x.property : ℝ≥0∞))) =
      ((μ.comap (Subtype.val : {x // 0 ≤ f x} → α)).map Subtype.val).withDensity
        (fun x => (w x : ℝ≥0∞)) := by
    ext s hss
    rw [Measure.map_apply measurable_subtype_coe hss,
      withDensity_apply _ (measurable_subtype_coe hss), withDensity_apply _ hss,
      setLIntegral_map hss hw.coe_nnreal_ennreal measurable_subtype_coe]
    apply setLIntegral_congr_fun (measurable_subtype_coe hss)
    intro x _
    simp [w, x.property]
  rw [he]
  erw [map_comap_subtype_coe hs, ← withDensity_indicator hs]
  congr 1
  funext x
  by_cases hx : 0 ≤ f x <;> simp [w, hx]
theorem exists_subtypeNonnegativeDensity_extension {A : Type*} [MeasurableSpace A]
    {s : Set A} (hs : MeasurableSet s) (f : s → ℝ≥0) (hf : Measurable f) :
    ∃ w : A → ℝ≥0, Measurable w ∧ (∀ x : s, w x.val = f x) ∧
      (∀ x, x ∉ s → w x = 0) ∧ ∀ μ : Measure A,
      Measure.map Subtype.val ((μ.comap (Subtype.val : s → A)).withDensity
        (fun x ↦ (f x : ℝ≥0∞))) = μ.withDensity (fun x ↦ (w x : ℝ≥0∞)) := by
  let w : A → ℝ≥0 := Function.extend Subtype.val f (fun _ ↦ 0)
  have hw : Measurable w :=
    (MeasurableEmbedding.subtype_coe hs).measurable_extend hf measurable_const
  have he (x : s) : w x.val = f x := Subtype.val_injective.extend_apply f (fun _ : A ↦ 0) x
  have hz (x : A) (hx : x ∉ s) : w x = 0 := by
    apply Function.extend_apply'
    rintro ⟨y,hy⟩
    exact hx (hy ▸ y.property)
  refine ⟨w,hw,he,hz,fun μ ↦ ?_⟩
  apply Measure.ext_of_lintegral
  intro φ hφ
  erw [(MeasurableEmbedding.subtype_coe hs).lintegral_map,
    lintegral_withDensity_eq_lintegral_mul _ hf.coe_nnreal_ennreal (hφ.comp measurable_subtype_coe),
    lintegral_withDensity_eq_lintegral_mul _ hw.coe_nnreal_ennreal hφ]
  calc
    _ = ∫⁻ x : s, (w x.val : ℝ≥0∞)*φ x.val ∂Measure.comap Subtype.val μ := by
      apply lintegral_congr
      intro x
      simp only [Pi.mul_apply,Function.comp_apply,he x]
    _ = ∫⁻ x in s, (w x : ℝ≥0∞)*φ x ∂μ :=
      lintegral_subtype_comap hs (fun x ↦ (w x : ℝ≥0∞)*φ x)
    _ = _ := by
      rw [← lintegral_indicator hs]
      congr 1
      funext x
      by_cases hx : x ∈ s
      · simp only [indicator_of_mem hx,Pi.mul_apply]
      · simp only [indicator_of_notMem hx,Pi.mul_apply,hz x hx,ENNReal.coe_zero,zero_mul]
end MeasureTheory
