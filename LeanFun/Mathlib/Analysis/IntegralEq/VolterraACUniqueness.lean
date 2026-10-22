/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.PolynomialVolterraUniqueness
public import LeanFun.Mathlib.MeasureTheory.Integral.IntegrableDerivative

/-! # First-kind uniqueness from regularity in the integration variable

Integration by parts transfers the equation to the continuous primitive of
an integrable input. Grönwall then proves uniqueness. Reference: Linz,
Analytical and Numerical Methods for Volterra Equations (1985), first-kind
uniqueness; Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Real

/-- Local integrability supplies every finite oriented input interval. -/
theorem intervalIntegrable_locallyIntegrable (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume) (x : ℝ) : IntervalIntegrable f volume 0 x :=
  intervalIntegrable_iff.mpr
    ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

/-- Interval integrability restricts to every initial subinterval. -/
theorem intervalIntegrable_of_integrableOn_Icc {f : ℝ → ℝ} {b x : ℝ}
    (hf : IntegrableOn f (Icc 0 b)) (hx : x ∈ Icc 0 b) :
    IntervalIntegrable f volume 0 x := by
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hx.1]
  exact hf.mono_set (fun y hy ↦ ⟨hy.1.le, hy.2.trans hx.2⟩)

/-- Absolutely continuous kernel slices preserve input integrability. -/
theorem intervalIntegrable_absolutelyContinuousKernel_mul
    {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hK : AbsolutelyContinuousOnInterval (fun y ↦ K ![x,y]) 0 x)
    (hf : IntervalIntegrable f volume 0 x) :
    IntervalIntegrable (fun y ↦ K ![x,y]*f y) volume 0 x :=
  hf.continuousOn_mul hK.continuousOn

/-- Absolutely continuous slices and integrable inputs give classical row pairs. -/
def VolterraIntegralInput.ofAbsolutelyContinuous
    {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hK : AbsolutelyContinuousOnInterval (fun y ↦ K ![x,y]) 0 x)
    (hf : IntervalIntegrable f volume 0 x) : VolterraIntegralInput x :=
  .ofKernel K f (intervalIntegrable_absolutelyContinuousKernel_mul hK hf)


/-- Volterra integrals on a subinterval depend only on the input's local almost-everywhere class. -/
theorem volterraIntegral_congr_ae_on (K : (Fin 2 → ℝ) → ℝ)
    {f g : ℝ → ℝ} {b x : ℝ} (hx : x ∈ Icc 0 b)
    (hfg : f =ᵐ[volume.restrict (Icc 0 b)] g)
    (hf : IntervalIntegrable (fun y ↦ K ![x,y]*f y) volume 0 x)
    (hg : IntervalIntegrable (fun y ↦ K ![x,y]*g y) volume 0 x) :
    volterraIntegral (.ofKernel K f hf) = volterraIntegral (.ofKernel K g hg) := by
  simp only [volterraIntegral_ofKernel]
  apply intervalIntegral.integral_congr_ae_restrict
  have hs : Set.uIoc 0 x ⊆ Icc 0 b := by
    rw [uIoc_of_le hx.1]
    exact fun y hy ↦ ⟨hy.1.le,hy.2.trans hx.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hfg] with y hy
  rw [hy]

/-- A homogeneous first-kind equation forces the input primitive to vanish. -/
theorem primitive_eq_zero_of_volterraIntegral_eq_zero
    {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ} {b C : ℝ}
    (hf : LocallyIntegrable f volume)
    (hAC : ∀ x ∈ Icc 0 b,
      AbsolutelyContinuousOnInterval (fun y ↦ K ![x,y]) 0 x)
    (hd : ∀ x ∈ Icc 0 b, K ![x,x] ≠ 0)
    (hb : ∀ x ∈ Icc 0 b,
      ∃ g : IntegrableDerivative (fun t ↦ K ![x,t]) (volume.restrict (uIcc 0 x)),
        ∀ᵐ y ∂volume.restrict (uIcc 0 x), ‖g y‖ ≤ C*|K ![x,x]|)
    (hz : ∀ x (hx : x ∈ Icc 0 b),
      volterraIntegral (.ofAbsolutelyContinuous (hAC x hx)
        (intervalIntegrable_locallyIntegrable f hf x)) = 0) :
    ∀ x ∈ Icc 0 b, (∫ y in (0 : ℝ)..x, f y) = 0 := by
  let F : ℝ → ℝ := fun x ↦ ∫ y in (0 : ℝ)..x, f y
  have hi (a c : ℝ) : IntervalIntegrable f volume a c :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hF : Continuous F := intervalIntegral.continuous_primitive hi 0
  apply eq_zero_of_norm_le_volterra_integral (M := C) hF
  intro x hx
  obtain ⟨g,hg⟩ := hb x hx
  have hder : ∀ᵐ y ∂volume.restrict (Icc 0 x), ‖g y‖ ≤ C*|K ![x,x]| := by
    simpa only [uIcc_of_le hx.1] using hg
  have hFa : AbsolutelyContinuousOnInterval F 0 x :=
    (hi 0 x).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  let k : IntegrableDerivative F (volume.restrict (uIcc 0 x)) :=
    ⟨⟨f, (intervalIntegrable_iff').mp (hi 0 x)⟩, by
      filter_upwards [ae_restrict_of_ae (LocallyIntegrable.ae_hasDerivAt_integral hf)] with y hy
      exact hy 0⟩
  have hp := g.integral_mul_eq_sub k (hAC x hx) hFa
  have he : (∫ y in (0 : ℝ)..x, K ![x,y] * k y) = volterraIntegral
      (.ofAbsolutelyContinuous (hAC x hx) (intervalIntegrable_locallyIntegrable f hf x)) := by
    rw [VolterraIntegralInput.ofAbsolutelyContinuous, volterraIntegral_ofKernel]
  have hF0 : F 0 = 0 := by simp [F]
  rw [he,hz x hx,hF0,mul_zero,sub_zero] at hp
  have hid : K ![x,x]*F x = ∫ y in (0 : ℝ)..x, g y * F y :=
    sub_eq_zero.mp hp.symm
  have hbnd : ‖K ![x,x]*F x‖ ≤
      C*|K ![x,x]| * (∫ y in (0 : ℝ)..x, ‖F y‖) := by
    rw [hid]
    apply (intervalIntegral.norm_integral_le_integral_norm hx.1).trans
    calc
      _ ≤ ∫ y in (0 : ℝ)..x, (C*|K ![x,x]|)*‖F y‖ := by
        apply intervalIntegral.integral_mono_ae_restrict hx.1
          ((((intervalIntegrable_iff').mpr g.integrable).mul_continuousOn hF.continuousOn).norm)
          ((hF.norm.const_mul (C*|K ![x,x]|)).intervalIntegrable _ _)
        filter_upwards [hder] with y hy
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [norm_mul, Real.norm_eq_abs] at hbnd
  apply (mul_le_mul_iff_left₀ (abs_pos.mpr (hd x hx))).mp
  convert hbnd using 1 <;> ring

/-- Absolutely continuous kernel slices with a uniform relative derivative bound give L¹ uniqueness. -/
theorem ae_eq_zero_of_volterraIntegral_eq_zero
    {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ} {b C : ℝ}
    (hf : LocallyIntegrable f volume)
    (hAC : ∀ x ∈ Icc 0 b,
      AbsolutelyContinuousOnInterval (fun y ↦ K ![x,y]) 0 x)
    (hd : ∀ x ∈ Icc 0 b, K ![x,x] ≠ 0)
    (hb : ∀ x ∈ Icc 0 b,
      ∃ g : IntegrableDerivative (fun t ↦ K ![x,t]) (volume.restrict (uIcc 0 x)),
        ∀ᵐ y ∂volume.restrict (uIcc 0 x), ‖g y‖ ≤ C*|K ![x,x]|)
    (hz : ∀ x (hx : x ∈ Icc 0 b),
      volterraIntegral (.ofAbsolutelyContinuous (hAC x hx)
        (intervalIntegrable_locallyIntegrable f hf x)) = 0) :
    f =ᵐ[volume.restrict (Icc 0 b)] 0 := by
  have hF := primitive_eq_zero_of_volterraIntegral_eq_zero hf hAC hd hb hz
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
  filter_upwards [ae_restrict_of_ae (LocallyIntegrable.ae_hasDerivAt_integral hf),
    self_mem_ae_restrict measurableSet_Ioo] with x hx hxi
  have he : (fun x ↦ ∫ y in (0 : ℝ)..x, f y) =ᶠ[𝓝 x] fun _ ↦ 0 :=
    Filter.Eventually.mono (isOpen_Ioo.mem_nhds hxi) (fun y hy ↦ hF y ⟨hy.1.le,hy.2.le⟩)
  exact (hx 0).unique ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he)

/-- The same uniqueness result only needs integrability on the interval under consideration. -/
theorem ae_eq_zero_of_integrableOn_volterraIntegral_eq_zero
    {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ} {b C : ℝ}
    (hf : IntegrableOn f (Icc 0 b))
    (hAC : ∀ x ∈ Icc 0 b,
      AbsolutelyContinuousOnInterval (fun y ↦ K ![x,y]) 0 x)
    (hd : ∀ x ∈ Icc 0 b, K ![x,x] ≠ 0)
    (hb : ∀ x ∈ Icc 0 b,
      ∃ g : IntegrableDerivative (fun t ↦ K ![x,t]) (volume.restrict (uIcc 0 x)),
        ∀ᵐ y ∂volume.restrict (uIcc 0 x), ‖g y‖ ≤ C*|K ![x,x]|)
    (hz : ∀ x (hx : x ∈ Icc 0 b),
      volterraIntegral (.ofAbsolutelyContinuous (hAC x hx)
        (intervalIntegrable_of_integrableOn_Icc hf hx)) = 0) :
    f =ᵐ[volume.restrict (Icc 0 b)] 0 := by
  let g := (Icc 0 b).indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Icc
  have hgf : g =ᵐ[volume.restrict (Icc 0 b)] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    exact indicator_of_mem hx f
  have hgz : ∀ x (hx : x ∈ Icc 0 b),
      volterraIntegral (.ofAbsolutelyContinuous (hAC x hx)
        (intervalIntegrable_locallyIntegrable g hg.locallyIntegrable x)) = 0 := by
    intro x hx
    have he := volterraIntegral_congr_ae_on K hx hgf
      (intervalIntegrable_absolutelyContinuousKernel_mul (hAC x hx)
        (intervalIntegrable_locallyIntegrable g hg.locallyIntegrable x))
      (intervalIntegrable_absolutelyContinuousKernel_mul (hAC x hx)
        (intervalIntegrable_of_integrableOn_Icc hf hx))
    exact he.trans (hz x hx)
  exact hgf.symm.trans (ae_eq_zero_of_volterraIntegral_eq_zero hg.locallyIntegrable hAC hd hb hgz)

end Real
