/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.MeasureTheory.VectorMeasure.AbsolutelyContinuous
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Bounded-variation estimates on a compact interval

Constant extension connects the global Stieltjes API to interval estimates,
including the bounded-variation base case of ATAP, Theorem 7.1.
-/

public section

open Set MeasureTheory intervalIntegral Filter
open scoped Topology NNReal

namespace BoundedVariationOn

/-- Constant extension does not increase variation. -/
theorem eVariationOn_comp_projIcc_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    eVariationOn (fun x ↦ f (projIcc a b hab x)) univ ≤ eVariationOn f (Icc a b) := by
  exact eVariationOn.comp_le_of_monotoneOn f (fun x ↦ (projIcc a b hab x : ℝ))
    (fun x _ y _ hxy ↦ monotone_projIcc hab hxy) (fun x _ ↦ (projIcc a b hab x).property)

/-- Constant extension of a function of bounded variation on an interval. -/
theorem comp_projIcc {f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    BoundedVariationOn (fun x ↦ f (projIcc a b hab x)) univ :=
  ne_top_of_le_ne_top hf (eVariationOn_comp_projIcc_le hab)

/-- Away from the two endpoints, the derivative of a constant extension is the
original derivative on the interval and zero outside it. -/
theorem ae_hasDerivAt_comp_projIcc {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) :
    ∀ᵐ x ∂volume, HasDerivAt (fun y ↦ g (projIcc a b hab y)) ((Icc a b).indicator g' x) x := by
  filter_upwards [(countable_singleton a).ae_notMem volume,
    (countable_singleton b).ae_notMem volume] with x hxa hxb
  simp only [mem_singleton_iff] at hxa hxb
  by_cases hx : x ∈ Icc a b
  · have hxo : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    rw [indicator_of_mem hx]
    apply (hg x hxo).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hxo.1 hxo.2] with y hy
    simp [projIcc_of_mem hab (Ioo_subset_Icc_self hy)]
  · rw [indicator_of_notMem hx]
    rcases lt_or_ge x a with hleft | hleft
    · apply (hasDerivAt_const x (g a)).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hleft] with y hy
      simp [projIcc_of_le_left hab hy.le]
    · have hright : b < x := lt_of_not_ge (fun h ↦ hx ⟨hleft, h⟩)
      apply (hasDerivAt_const x (g b)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hright] with y hy
      simp [projIcc_of_right_le hab hy.le]

/-- Integration against the derivative of a Lipschitz primitive that vanishes at
both endpoints is bounded by its supremum times the variation on the interval. -/
theorem abs_integral_mul_le_of_lipschitz_primitive {f g g' : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    {K : ℝ≥0} (hg : LipschitzWith K g)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hint : IntervalIntegrable g' volume a b) (ha : g a = 0) (hb : g b = 0)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ Icc a b, |g x| ≤ C) :
    |∫ x in a..b, g' x * f x| ≤ C * (eVariationOn f (Icc a b)).toReal := by
  let F : ℝ → ℝ := fun x ↦ f (projIcc a b hab x)
  let G : ℝ → ℝ := fun x ↦ g (projIcc a b hab x)
  let H : ℝ → ℝ := (Icc a b).indicator g'
  have hF : BoundedVariationOn F univ := hf.comp_projIcc hab
  have hG : BoundedVariationOn G univ :=
    (hg.comp_boundedVariationOn (BoundedVariationOn.id_Icc a b)).comp_projIcc hab
  have hGL : LipschitzWith (K * 1) G :=
    by simpa only [one_mul, Function.comp_def, G] using
      hg.comp ((LipschitzWith.subtype_val (Icc a b)).comp (LipschitzWith.projIcc hab))
  have hH : Integrable H := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab enorm_ne_top).1 hint
      |>.integrable_indicator measurableSet_Icc
  have hder : ∀ᵐ x ∂volume, HasDerivAt G (H x) x := ae_hasDerivAt_comp_projIcc hab hd
  have hFTC (u v : ℝ) (_huv : u ≤ v) : ∫ x in u..v, H x = G v - G u := by
    let d : IntegrableDerivative G (volume.restrict (uIcc u v)) :=
      ⟨⟨H, hH.restrict⟩, ae_restrict_of_ae hder⟩
    exact d.integral_eq_sub hGL.lipschitzOnWith.absolutelyContinuousOnInterval
  have hI := hF.abs_integral_mul_le_of_primitive hG hGL.continuous hH hFTC hab
    (by simpa [G] using ha) (by simpa [G] using hb) hC
    (fun x hx ↦ by simpa [G, projIcc_of_mem hab hx] using hbound x hx)
  have heq : (∫ x in a..b, H x * F x) = ∫ x in a..b, g' x * f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc a b := by simpa [uIcc_of_le hab] using hx
    simp [H, F, indicator_of_mem hx', projIcc_of_mem hab hx']
  rw [heq] at hI
  apply hI.trans
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hf (eVariationOn_comp_projIcc_le hab)) hC

end BoundedVariationOn
