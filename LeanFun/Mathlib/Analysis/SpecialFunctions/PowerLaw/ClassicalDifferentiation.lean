/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Calculus.Deriv.OpenDomain
public import Mathlib.Basic.Real.Sign
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Differentiation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalWeighted
/-! # Classical convolution and power-law differentiation

Integrability is bundled in the input and kernels carry their actual continuous
derivative. The power kernel derivative is defined also at zero without a
negative power of zero. Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, §2.
-/
@[expose] public section
open Set MeasureTheory Polynomial Filter
open scoped Topology NNReal
noncomputable section
namespace Real
local notation "μI" => Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume

structure C1ConvolutionKernel where
  value : C(ℝ,ℝ)
  slope : C(ℝ,ℝ)
  hasDeriv : ∀ x, HasDerivAt value (slope x) x

def convolutionInput (g : C(ℝ,ℝ)) (x : ℝ) (f : IntegrableInput μI) : IntegrableInput μI := by
  refine ⟨fun y ↦ g (x-y.val)*f.val y, ?_⟩
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := x-1) (b := x+1)).exists_bound_of_continuousOn
    g.continuous.continuousOn
  apply f.property.bdd_mul
    (g.continuous.comp (continuous_const.sub continuous_subtype_val)).aestronglyMeasurable
  exact Eventually.of_forall (fun y ↦ hM (x-y.val) ⟨by linarith [y.property.2],by linarith [y.property.1]⟩)

def intervalConvolution (g : C(ℝ,ℝ)) (f : IntegrableInput μI) (x : ℝ) : ℝ :=
  ∫ y, (convolutionInput g x f).val y ∂μI

theorem convolutionInput_apply (g : C(ℝ,ℝ)) (x : ℝ) (f : IntegrableInput μI)
    (y : Ioo (-1 : ℝ) 1) : (convolutionInput g x f).val y = g (x-y.val)*f.val y := rfl

theorem intervalConvolution_apply (g : C(ℝ,ℝ)) (f : IntegrableInput μI) (x : ℝ) :
    intervalConvolution g f x = ∫ y : Ioo (-1 : ℝ) 1, g (x-y.val)*f.val y ∂μI := rfl

theorem IntegrableInput.exists_openIntervalRepresentative (f : IntegrableInput μI) :
    ∃ F : ℝ → ℝ, (∀ y : Ioo (-1 : ℝ) 1, F y.val = f.val y) ∧
      IntervalIntegrable F volume (-1) 1 := by
  let F : ℝ → ℝ := Function.extend Subtype.val f.val (fun _ ↦ 0)
  have he (y : Ioo (-1 : ℝ) 1) : F y.val = f.val y :=
    Subtype.val_injective.extend_apply _ _ y
  refine ⟨F,he,?_⟩
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mpr
  apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mpr
  change Integrable (fun y : Ioo (-1 : ℝ) 1 ↦ F y.val) μI
  simpa only [he] using f.property

theorem intervalConvolution_eq_interval (g : C(ℝ,ℝ)) (f : IntegrableInput μI) (F : ℝ → ℝ)
    (he : ∀ y : Ioo (-1 : ℝ) 1, F y.val = f.val y) (x : ℝ) :
    intervalConvolution g f x = ∫ y in (-1 : ℝ)..1, g (x-y)*F y := by
  rw [intervalConvolution_apply]
  simp_rw [← he]
  rw [integral_subtype_comap (μ := volume) measurableSet_Ioo (fun y : ℝ ↦ g (x-y)*F y),
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]

theorem hasDerivAt_intervalConvolution (g : C1ConvolutionKernel) (f : IntegrableInput μI)
    (x : Ioo (-1 : ℝ) 1) :
    HasDerivAt (intervalConvolution g.value f) (intervalConvolution g.slope f x.val) x.val := by
  obtain ⟨F,he,hF⟩ := IntegrableInput.exists_openIntervalRepresentative f
  have hd : deriv g.value = g.slope := funext (fun t ↦ (g.hasDeriv t).deriv)
  have h := hasDerivAt_intervalIntegral_sub_mul
    (fun t ↦ (g.hasDeriv t).differentiableAt) (by rw [hd]; exact g.slope.continuous) hF x.property
  rw [hd] at h
  have hfun : intervalConvolution g.value f = fun t ↦ ∫ y in (-1 : ℝ)..1, g.value (t-y)*F y :=
    funext (intervalConvolution_eq_interval g.value f F he)
  rw [hfun,intervalConvolution_eq_interval g.slope f F he]
  exact h
end Real
namespace Real
local notation "μI" => Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume

def absPowerKernel (β : ℝ≥0) : C(ℝ,ℝ) :=
  ⟨fun t ↦ |t|^(β : ℝ), continuous_abs.rpow_const (fun _ ↦ Or.inr β.property)⟩

theorem absPowerKernel_apply (β : ℝ≥0) (t : ℝ) : absPowerKernel β t = |t|^(β : ℝ) := rfl

def PowerLawInput.ofL1 (β : ℝ≥0) (x : ℝ) (f : IntegrableInput μI) : PowerLawInput β x := by
  refine ⟨fun y ↦ f.val ⟨y.val,y.property.1⟩, ?_⟩
  have h := (integrable_integral_powerLawDomain x (convolutionInput (absPowerKernel β) x f)).1
  convert h using 1
  all_goals rfl

theorem PowerLawInput.ofL1_apply (β : ℝ≥0) (x : ℝ) (f : IntegrableInput μI)
    (y : PowerLawDomain x) : (PowerLawInput.ofL1 β x f).val y = f.val ⟨y.val,y.property.1⟩ := rfl

theorem powerLawIntegral_ofL1_eq_convolution (β : ℝ≥0) (x : ℝ) (f : IntegrableInput μI) :
    powerLawIntegral (.ofL1 β x f) = intervalConvolution (absPowerKernel β) f x := by
  rw [intervalConvolution_apply]
  have h := (integrable_integral_powerLawDomain x (convolutionInput (absPowerKernel β) x f)).2
  convert h using 1
  all_goals rfl

theorem hasDerivAt_absPowerKernel (β : Ioi (1 : ℝ)) (t : ℝ) :
    HasDerivAt (absPowerKernel ⟨β.val,by have hb : 1 < β.val := β.property; linarith⟩)
      (β.val*|t|^(β.val-1)*sign t) t := by
  have hb : 1 < β.val := β.property
  change HasDerivAt (fun x : ℝ ↦ |x|^β.val) _ t
  have h := hasDerivAt_abs_rpow t hb
  convert h using 1
  by_cases ht : t = 0
  · subst t
    simp
  · have ha : 0 < |t| := abs_pos.mpr ht
    have hr : |t|^(β.val-1) = |t|^(β.val-2)*|t| := by
      rw [← rpow_add_one ha.ne']
      congr 1
      ring
    have hs : |t| * sign t = t := by
      rcases lt_or_gt_of_ne ht with hn | hp
      · rw [abs_of_neg hn, sign_of_neg hn]; ring
      · rw [abs_of_pos hp, sign_of_pos hp, mul_one]
    rw [hr, mul_assoc, mul_assoc, hs]
    ring
end Real

namespace Real
local notation "μI" => Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume

def C1ConvolutionKernel.power (β : Ioi (1 : ℝ)) : C1ConvolutionKernel where
  value := absPowerKernel ⟨β.val,by have hb : 1 < β.val := β.property; linarith⟩
  slope := ⟨fun t ↦ β.val*|t|^(β.val-1)*sign t, by
    have hb : 1 < β.val := β.property
    have hg : ContDiff ℝ 1 (fun t : ℝ ↦ |t|^β.val) := by
      simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow (E := ℝ) hb)
    have he : deriv (fun t : ℝ ↦ |t|^β.val) = fun t ↦ β.val*|t|^(β.val-1)*sign t :=
      funext (fun t ↦ (hasDerivAt_absPowerKernel β t).deriv)
    rw [← he]
    exact hg.continuous_deriv_one⟩
  hasDeriv := hasDerivAt_absPowerKernel β

theorem C1ConvolutionKernel.power_value (β : Ioi (1 : ℝ)) (t : ℝ) :
    (C1ConvolutionKernel.power β).value t = |t|^β.val := rfl

theorem C1ConvolutionKernel.power_slope (β : Ioi (1 : ℝ)) (t : ℝ) :
    (C1ConvolutionKernel.power β).slope t = β.val*|t|^(β.val-1)*sign t := rfl

theorem hasDerivAt_powerLawIntegralOn (β : Ioi (1 : ℝ)) (f : IntegrableInput μI)
    (x : Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t ↦ powerLawIntegral (.ofL1
      ⟨β.val,by have hb : 1 < β.val := β.property; linarith⟩ t f))
      (intervalConvolution (C1ConvolutionKernel.power β).slope f x.val) x.val := by
  have he : (fun t ↦ powerLawIntegral (.ofL1
      ⟨β.val,by have hb : 1 < β.val := β.property; linarith⟩ t f)) =
      intervalConvolution (C1ConvolutionKernel.power β).value f :=
    funext (fun t ↦ powerLawIntegral_ofL1_eq_convolution _ t f)
  rw [he]
  exact hasDerivAt_intervalConvolution (C1ConvolutionKernel.power β) f x
end Real

namespace Real
attribute [local instance] Measure.Subtype.measureSpace
local notation "μI" => Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume

theorem powerLawIntegral_gegenbauer_one_hasDerivOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    ∃ d : ℝ, HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1,isOpen_Ioo⟩
      (fun t ↦ powerLawIntegral (.gegenbauerWeight
        ⟨α.val+2,by change -1 < α.val+2; have hα : -1 < α.val := α.property; linarith⟩ lam t)) d x ∧
      powerLawIntegral (.gegenbauerMode α lam x 1) =
        2*lam.val*(x.val*powerLawIntegral (.gegenbauerWeight α lam x)-d/(α.val+2)) := by
  have hα : -1 < α.val := α.property
  have hb : 0 < α.val+2 := by linarith
  let β : Ioi (1 : ℝ) := ⟨α.val+2,by change 1 < α.val+2; linarith⟩
  let f : IntegrableInput μI := ⟨fun y ↦ (gegenbauerWeight lam.val y : ℝ),
    integrable_gegenbauerWeight lam.property⟩
  let g := C1ConvolutionKernel.power β
  let d := intervalConvolution g.slope f x.val
  refine ⟨d, ?_, ?_⟩
  · refine ⟨intervalConvolution g.value f, ?_, hasDerivAt_intervalConvolution g f x⟩
    intro t
    erw [← powerLawIntegral_ofL1_eq_convolution]
    congr 1
    apply Subtype.ext
    funext y
    change (gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ) = _
    exact (PowerLawInput.gegenbauerWeight_apply _ lam t y).symm
  · let s := convolutionInput g.slope x.val f
    have hs := integrable_integral_powerLawDomain x.val s
    let H := fun y : PowerLawDomain x.val ↦
      |x.val-y.val|^α.val * (gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ)
    let S := fun y : PowerLawDomain x.val ↦ s.val ⟨y.val,y.property.1⟩
    have hH : Integrable H (Measure.comap Subtype.val volume) := by
      simpa only [H, PowerLawInput.gegenbauerWeight_apply] using
        (PowerLawInput.gegenbauerWeight α lam x).property
    have hS : Integrable S (Measure.comap Subtype.val volume) := hs.1
    have hd : (∫ y, S y ∂Measure.comap Subtype.val volume) = d := hs.2
    have he (y : PowerLawDomain x.val) :
        |x.val-y.val|^α.val * (PowerLawInput.gegenbauerMode α lam x 1).val y =
          2*lam.val*(x.val*H y-S y/(α.val+2)) := by
      rw [PowerLawInput.gegenbauerMode_apply, gegenbauer_one]
      simp only [eval_mul, eval_C, eval_X]
      have ha := powerLawDomain_base_pos y
      have hp : |x.val-y.val|^(α.val+2-1) = |x.val-y.val|^α.val*|x.val-y.val| := by
        rw [show α.val+2-1 = α.val+1 by ring, rpow_add_one ha.ne']
      have hsign : |x.val-y.val| *sign (x.val-y.val) = x.val-y.val := by
        rcases lt_or_gt_of_ne (sub_ne_zero.mpr y.property.2.symm) with hn | hp
        · rw [abs_of_neg hn, sign_of_neg hn]; ring
        · rw [abs_of_pos hp, sign_of_pos hp, mul_one]
      change _ = 2*lam.val*(x.val*H y-
        ((α.val+2)*|x.val-y.val|^(α.val+2-1)*sign (x.val-y.val)*
          (gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ))/(α.val+2))
      rw [hp]
      have hslope : (α.val+2) * (|x.val-y.val|^α.val*|x.val-y.val|) *
          sign (x.val-y.val) = (α.val+2)*|x.val-y.val|^α.val*(x.val-y.val) := by
        calc
          _ = (α.val+2)*|x.val-y.val|^α.val*
            (|x.val-y.val| *sign (x.val-y.val)) := by ring
          _ = _ := by rw [hsign]
      rw [hslope]
      dsimp only [H]
      field_simp [hb.ne']
      ring
    change (∫ y, |x.val-y.val|^α.val * (PowerLawInput.gegenbauerMode α lam x 1).val y
      ∂Measure.comap Subtype.val volume) = _
    simp_rw [he]
    rw [integral_const_mul, integral_sub (hH.const_mul _) (hS.div_const _),
      integral_const_mul, integral_div, hd]
    simp only [powerLawIntegral, PowerLawInput.gegenbauerWeight_apply, H]

end Real
