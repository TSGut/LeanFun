/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-! # Certified product measures

A measurable product kernel ensures that the product is the classical iterated
measure. S-finite inner factors supply this certificate automatically.
Reference: the measurable-kernel construction of product measures and Tonelli’s theorem.
-/
@[expose] public section
open MeasureTheory
noncomputable section
namespace MeasureTheory
/-- Inner measures with a certified product kernel over the outer measure. -/
structure ProductMeasureInput {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) where
  inner : Measure β
  measurable : AEMeasurable (fun x : α ↦ Measure.map (Prod.mk x) inner) μ

abbrev ProductMeasureInput.ofSFinite {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [hν : SFinite ν] : ProductMeasureInput (β := β) μ :=
  ⟨ν,Measurable.map_prodMk_left.aemeasurable⟩

theorem ProductMeasureInput.prod_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} (ν : ProductMeasureInput (β := β) μ) {s : Set (α × β)}
    (hs : MeasurableSet s) :
    (μ.prod ν.inner) s = ∫⁻ x, ν.inner ((Prod.mk x) ⁻¹' s) ∂μ := by
  rw [Measure.prod, Measure.bind_apply hs ν.measurable]
  apply lintegral_congr
  intro x
  exact Measure.map_apply measurable_prodMk_left hs
end MeasureTheory
