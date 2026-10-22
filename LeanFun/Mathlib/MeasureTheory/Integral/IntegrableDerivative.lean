/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.MeasureTheory.Integral.ClassicalWeight
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Integrable representatives of almost-everywhere derivatives

A representative is an integrable function certified by `HasDerivAt` almost
everywhere. Values on exceptional null sets are representative values, not
assertions of pointwise derivatives. References: the fundamental theorem for
absolutely continuous functions; ATAP Chapter 7; Linz, Volterra equations.
-/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- An integrable representative of a derivative, with existence certified a.e. -/
structure IntegrableDerivative (f : ℝ → ℝ) (μ : Measure ℝ) where
  input : IntegrableInput μ
  hasDerivAt : ∀ᵐ x ∂μ, HasDerivAt f (input.val x) x

namespace IntegrableDerivative
instance {f : ℝ → ℝ} {μ : Measure ℝ} : CoeFun (IntegrableDerivative f μ) (fun _ => ℝ → ℝ) :=
  ⟨fun g => g.input.val⟩

theorem integrable {f : ℝ → ℝ} {μ : Measure ℝ} (g : IntegrableDerivative f μ) :
    Integrable g μ := g.input.property

theorem unique {f : ℝ → ℝ} {μ : Measure ℝ} (g h : IntegrableDerivative f μ) :
    (g : ℝ → ℝ) =ᵐ[μ] h := by
  filter_upwards [g.hasDerivAt,h.hasDerivAt] with x hg hh
  exact hg.unique hh


private theorem monotone_representative {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) :
    Nonempty (IntegrableDerivative f (volume.restrict (Icc a b))) := by
  classical
  let h (x : ℝ) := f (max a (min x b))
  have hh : Monotone h := monotoneOn_univ.mp <| hf.comp
    (monotoneOn_const.max <| monotoneOn_id.min monotoneOn_const) (by simpa)
  have hfh : EqOn f h (Ioo a b) := fun x ⟨hxa, hxb⟩ => congrArg f <|
    min_eq_left hxb.le |>.symm ▸ (max_eq_right hxa.le).symm
  let d (x : ℝ) := if hx : DifferentiableAt ℝ h x then deriv h x else 0
  have hd : ∀ᵐ x, HasDerivAt h (d x) x := by
    filter_upwards [hh.ae_differentiableAt] with x hx
    simpa only [d, dite_eq_left hx] using hx.hasDerivAt
  let c (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  let G (n : ℕ) (x : ℝ) := slope h x (x + c n)
  have hGi (n : ℕ) : Integrable (G n) (volume.restrict (Icc a b)) := by
    have := hh.monotoneOn (Icc a (b + c n)) |>.intervalIntegrable_slope hab (hc n).le
    exact intervalIntegrable_iff_integrableOn_Icc_of_le hab |>.mp this
  have hlim : ∀ᵐ x ∂volume.restrict (Icc a b),
      Tendsto (fun n ↦ G n x) atTop (𝓝 (d x)) := by
    filter_upwards [ae_restrict_of_ae hd] with x hx
    apply hx.tendsto_slope.comp
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have ht : Tendsto c atTop (𝓝 0) := by
        simpa only [c, Function.comp_def, Nat.cast_add, Nat.cast_one] using
          (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      simpa using tendsto_const_nhds.add ht
    · filter_upwards with n
      simp only [mem_compl_iff, mem_singleton_iff]
      linarith [hc n]
  have hbound : liminf (fun n ↦ ∫⁻ x in Icc a b, ‖G n x‖ₑ) atTop ≤
      ENNReal.ofReal (h b - h a) := by
    calc
      _ = liminf (fun n ↦ ENNReal.ofReal (∫ x in Icc a b, G n x)) atTop := by
        apply Filter.liminf_congr
        filter_upwards with n
        rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hGi n)]
        congr with y
        exact abs_eq_self.mpr (hh.monotoneOn univ |>.slope_nonneg trivial trivial)
      _ ≤ _ := by
        refine Filter.liminf_le_of_frequently_le'
          (Filter.Frequently.of_forall fun n ↦ ENNReal.ofReal_le_ofReal ?_)
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
        have hend : h (b + c n) = h b := by
          dsimp only [h]
          rw [min_eq_right (by linarith [hc n]), min_self]
        simpa only [G, hend] using
          (hh.monotoneOn (Icc a (b + c n)) |>.intervalIntegral_slope_le hab (hc n).le)
  have hi : Integrable d (volume.restrict (Icc a b)) :=
    integrable_of_tendsto hlim (fun n ↦ (hGi n).aestronglyMeasurable)
      (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top).ne_top
  refine ⟨⟨⟨d, hi⟩, ?_⟩⟩
  change ∀ᵐ x ∂volume.restrict (Icc a b), HasDerivAt f (d x) x
  rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hd] with x hx hmem
  exact hx.congr_of_eventuallyEq (hfh.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hmem))

private theorem bv_representative {f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedVariationOn f (uIcc a b)) :
    Nonempty (IntegrableDerivative f (volume.restrict (uIcc a b))) := by
  wlog hab : a ≤ b generalizing a b
  · simpa only [uIcc_comm b a] using this (uIcc_comm a b ▸ hf) (le_of_not_ge hab)
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  rw [uIcc_of_le hab] at hp hq ⊢
  obtain ⟨dp⟩ := monotone_representative hab hp
  obtain ⟨dq⟩ := monotone_representative hab hq
  refine ⟨⟨⟨fun x ↦ dp x - dq x, dp.integrable.sub dq.integrable⟩, ?_⟩⟩
  filter_upwards [dp.hasDerivAt, dq.hasDerivAt] with x hx hy
  exact hx.sub hy

/-- Absolute continuity supplies classical integrable derivative data. -/
theorem nonempty_of_absolutelyContinuous {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    Nonempty (IntegrableDerivative f (volume.restrict (uIcc a b))) := by
  exact bv_representative hf.boundedVariationOn



/-- FTC for a certified integrable derivative representative; the classical AC theorem. -/
theorem integral_eq_sub {f : ℝ → ℝ} {a b : ℝ}
    (g : IntegrableDerivative f (volume.restrict (uIcc a b)))
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ x in a..b, g x = f b - f a := by
  let G : ℝ → ℝ := (uIcc a b).indicator g
  have hGi : Integrable G := (integrable_indicator_iff measurableSet_uIcc).mpr g.integrable
  have hg : IntervalIntegrable G volume a b := hGi.intervalIntegrable
  have hG := hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x :=
    (ae_restrict_iff' measurableSet_uIcc).mp g.hasDerivAt
  have hz : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun y ↦ f y - ∫ t in a..y, G t) 0 x := by
    filter_upwards [hd, hg.ae_hasDerivAt_integral] with x hx hGx hmem
    convert (hx hmem).sub (hGx hmem a (by simp)) using 1
    simp only [G, Set.indicator_of_mem hmem, sub_self]
  obtain ⟨C, hC⟩ := (hf.sub hG).const_of_ae_hasDerivAt_zero hz
  have ha := hC a (by simp)
  have hb := hC b (by simp)
  change f a - (∫ t in a..a, G t) = C at ha
  change f b - (∫ t in a..b, G t) = C at hb
  simp only [intervalIntegral.integral_same, sub_zero] at ha
  have he : (∫ x in a..b, G x) = ∫ x in a..b, g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact Set.indicator_of_mem hx g
  rw [he] at hb
  linarith

/-- Integration by parts for certified representatives (ATAP, Chapter 7). -/
theorem integral_mul_eq_sub {f h : ℝ → ℝ} {a b : ℝ}
    (g : IntegrableDerivative f (volume.restrict (uIcc a b)))
    (k : IntegrableDerivative h (volume.restrict (uIcc a b)))
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hh : AbsolutelyContinuousOnInterval h a b) :
    ∫ x in a..b, f x * k x = f b * h b - f a * h a - ∫ x in a..b, g x * h x := by
  have hg : IntervalIntegrable g volume a b := (intervalIntegrable_iff').mpr g.integrable
  have hk : IntervalIntegrable k volume a b := (intervalIntegrable_iff').mpr k.integrable
  have hgh := hg.mul_continuousOn hh.continuousOn
  have hfk := hk.continuousOn_mul hf.continuousOn
  let d : IntegrableDerivative (fun x ↦ f x * h x) (volume.restrict (uIcc a b)) :=
    ⟨⟨fun x ↦ g x * h x + f x * k x, (intervalIntegrable_iff').mp (hgh.add hfk)⟩, by
      filter_upwards [g.hasDerivAt, k.hasDerivAt] with x hx hy
      exact hx.mul hy⟩
  have he := d.integral_eq_sub (hf.fun_mul hh)
  change (∫ x in a..b, g x * h x + f x * k x) = _ at he
  rw [intervalIntegral.integral_add hgh hfk] at he
  linarith

end IntegrableDerivative
