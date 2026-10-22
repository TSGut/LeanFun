/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.PolynomialDensityMeasure

/-! # Polynomial density changes within a fixed outer domain

Reference: Gautschi, polynomial modifications of orthogonality measures;
Dunkl–Xu, separated polynomial systems.
-/

@[expose] public section
open MeasureTheory
open scoped NNReal ENNReal
namespace Polynomial
variable {D : Set ℝ}

/-- A nonnegative polynomial density on a source inside the fixed outer domain. -/
noncomputable def subtypeDensityMeasure (p : ℝ[X])
    (μ : Measure {x : D // 0 ≤ p.eval (x : ℝ)}) : Measure D :=
  Measure.map Subtype.val (μ.withDensity (fun x =>
    ENNReal.ofNNReal (NNReal.mk (p.eval (x.val : ℝ)) x.property)))

/-- Values on measurable sets are the nonnegative weighted source integrals. -/
theorem subtypeDensityMeasure_apply (p : ℝ[X])
    (μ : Measure {x : D // 0 ≤ p.eval (x : ℝ)}) {s : Set D} (hs : MeasurableSet s) :
    subtypeDensityMeasure p μ s = ∫⁻ x in Subtype.val ⁻¹' s,
      ENNReal.ofNNReal (NNReal.mk (p.eval (x.val : ℝ)) x.property) ∂μ := by
  rw [subtypeDensityMeasure, Measure.map_apply measurable_subtype_coe hs,
    withDensity_apply _ (measurable_subtype_coe hs)]

/-- A measurable extension transports a density within the outer domain. -/
theorem exists_subtypeDensityMeasure_extension (p : ℝ[X]) :
    ∃ w : D → ℝ≥0, Measurable w ∧
      (∀ (x : D) (hx : 0 ≤ p.eval (x : ℝ)), w x = NNReal.mk (p.eval (x : ℝ)) hx) ∧
      (∀ x : D, ¬ 0 ≤ p.eval (x : ℝ) → w x = 0) ∧
      ∀ μ : Measure D, subtypeDensityMeasure p (μ.comap Subtype.val) =
        μ.withDensity (fun x => (w x : ENNReal)) :=
  exists_nonnegativeDensity_extension (fun x : D => p.eval (x : ℝ))
    (p.continuous.measurable.comp measurable_subtype_coe)

/-- Domain density changes are absolutely continuous with respect to the source. -/
theorem subtypeDensityMeasure_comap_absolutelyContinuous (p : ℝ[X]) (μ : Measure D) :
    subtypeDensityMeasure p (μ.comap Subtype.val) ≪ μ := by
  obtain ⟨w, _, _, _, he⟩ := exists_subtypeDensityMeasure_extension (D := D) p
  rw [he]
  exact withDensity_absolutelyContinuous _ _

instance subtypeDensityMeasure_comap_sfinite (p : ℝ[X]) (μ : Measure D) [SFinite μ] :
    SFinite (subtypeDensityMeasure p (μ.comap Subtype.val)) := by
  obtain ⟨w, _, _, _, he⟩ := exists_subtypeDensityMeasure_extension (D := D) p
  rw [he]
  infer_instance

/-- Domain and real-coordinate density constructions commute with the coordinate map. -/
theorem map_subtypeDensityMeasure_comap (p : ℝ[X]) (μ : Measure D) :
    Measure.map Subtype.val (subtypeDensityMeasure p (μ.comap Subtype.val)) =
      polynomialDensityMeasure p ((μ.map Subtype.val).comap Subtype.val) := by
  obtain ⟨w, hw, hwval, hwzero, he⟩ := exists_subtypeDensityMeasure_extension (D := D) p
  obtain ⟨v, hv, hvval, hvzero, hf⟩ := exists_polynomialDensityMeasure_extension p
  rw [he, hf]
  ext s hs
  rw [Measure.map_apply measurable_subtype_coe hs,
    withDensity_apply _ (measurable_subtype_coe hs), withDensity_apply _ hs,
    setLIntegral_map hs hv.coe_nnreal_ennreal measurable_subtype_coe]
  apply setLIntegral_congr_fun (measurable_subtype_coe hs)
  intro x _
  change (w x : ENNReal) = (v (x : ℝ) : ENNReal)
  apply congrArg (fun a : ℝ≥0 => (a : ENNReal))
  by_cases hx : 0 ≤ p.eval (x : ℝ)
  · rw [hwval x hx, hvval (x : ℝ) hx]
  · rw [hwzero x hx, hvzero (x : ℝ) hx]

/-- Classical density modification commutes with restriction to a supported domain. -/
theorem comap_polynomialDensityMeasure_eq_subtypeDensityMeasure {D : Set ℝ} (hD : MeasurableSet D) (p : ℝ[X]) (μ : Measure ℝ)
    (hx : ∀ᵐ x ∂μ, x ∈ D) :
    (polynomialDensityMeasure p (μ.comap Subtype.val)).comap
        (Subtype.val : D → ℝ) =
      subtypeDensityMeasure p ((μ.comap (Subtype.val : D → ℝ)).comap Subtype.val) := by
  apply (MeasurableEmbedding.subtype_coe hD).map_injective
  rw [map_comap_subtype_coe hD,
    Measure.restrict_eq_self_of_ae_mem
      ((polynomialDensityMeasure_comap_absolutelyContinuous p μ).ae_le hx),
    map_subtypeDensityMeasure_comap, map_comap_subtype_coe hD,
    Measure.restrict_eq_self_of_ae_mem hx]

end Polynomial
