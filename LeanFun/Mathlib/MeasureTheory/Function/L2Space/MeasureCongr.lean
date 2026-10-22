/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.l2Space
/-! # Transport of L² function/gradient pairs across equal measures

An equality of measures identifies the scalar and finite Hilbert-sum L² spaces
isometrically, including their canonical classes of measurable representatives.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace MeasureTheory.L2
variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
/-- Equal measures give the same L² function/gradient graph space. -/
def graphMeasureCongr (n : ℕ) (h : μ = ν) :
    (Lp ℝ 2 μ × lp (fun _ : Fin n ↦ Lp ℝ 2 μ) 2) ≃ₗᵢ[ℝ]
    (Lp ℝ 2 ν × lp (fun _ : Fin n ↦ Lp ℝ 2 ν) 2) := by
  subst ν
  exact LinearIsometryEquiv.refl ℝ _
/-- Transport preserves the classes of a function and its gradient components. -/
theorem graphMeasureCongr_toLp (n : ℕ) (h : μ = ν) (f : X → ℝ) (g : Fin n → X → ℝ)
    (hfμ : MemLp f 2 μ) (hfν : MemLp f 2 ν)
    (hgμ : ∀ i, MemLp (g i) 2 μ) (hgν : ∀ i, MemLp (g i) 2 ν) :
    graphMeasureCongr n h (hfμ.toLp f, ∑ i, lp.single 2 i ((hgμ i).toLp (g i))) =
      (hfν.toLp f, ∑ i, lp.single 2 i ((hgν i).toLp (g i))) := by
  subst ν
  rfl
/-- Measure transport preserves the scalar L² inner product separately. -/
theorem graphMeasureCongr_inner_fst (n : ℕ) (h : μ = ν)
    (u v : Lp ℝ 2 μ × lp (fun _ : Fin n ↦ Lp ℝ 2 μ) 2) :
    inner ℝ (graphMeasureCongr n h u).1 (graphMeasureCongr n h v).1 = inner ℝ u.1 v.1 := by
  subst ν
  rfl
/-- Measure transport preserves the gradient Hilbert-sum inner product separately. -/
theorem graphMeasureCongr_inner_snd (n : ℕ) (h : μ = ν)
    (u v : Lp ℝ 2 μ × lp (fun _ : Fin n ↦ Lp ℝ 2 μ) 2) :
    inner ℝ (graphMeasureCongr n h u).2 (graphMeasureCongr n h v).2 = inner ℝ u.2 v.2 := by
  subst ν
  rfl
end MeasureTheory.L2
