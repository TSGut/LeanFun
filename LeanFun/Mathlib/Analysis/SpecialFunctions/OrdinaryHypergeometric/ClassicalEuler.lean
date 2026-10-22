/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.BetaDomain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.Real
import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.RealDomain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.ClassicalAnalytic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.RegularizedDomain
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Classical Euler moments and Gauss integrals
The integration domain is the open unit interval. Every integral assertion
includes or inherits integrability. References: DLMF5.12.1 and15.6.1.
-/
@[expose] public noncomputable section
open MeasureTheory Set Polynomial Filter


namespace Complex
open Polynomial
/-- The classical Beta shift formula on its full Euler domain. -/
theorem betaIntegralOn_add_nat_left (a b : BetaParameter) (n : ℕ) :
    betaIntegralOn ⟨a.val + n, by simp only [add_re, natCast_re]; exact add_pos_of_pos_of_nonneg a.property (Nat.cast_nonneg _)⟩ b =
      betaIntegralOn a b * (ascPochhammer ℂ n).eval a.val /
        (ascPochhammer ℂ n).eval (a.val + b.val) := by
  have hc : 0 < (a.val+b.val).re := by simpa only [add_re] using add_pos a.property b.property
  have hga := GammaOn_ne_zero (GammaPoint.ofRePos a.val a.property)
  have hgc := GammaOn_ne_zero (GammaPoint.ofRePos (a.val+b.val) hc)
  have hgcn := GammaOn_ne_zero ((GammaPoint.ofRePos (a.val+b.val) hc).addNat n)
  have hra := GammaOn_add_nat_div (GammaPoint.ofRePos a.val a.property) n
  have hrc := GammaOn_add_nat_div (GammaPoint.ofRePos (a.val+b.val) hc) n
  rw [betaIntegralOn_eq_Gamma,betaIntegralOn_eq_Gamma]
  simp only [GammaOn,GammaPoint.ofRePos,GammaPoint.addNat_val] at hga hgc hgcn hra hrc ⊢
  rw [← hra,← hrc,show a.val+n+b.val = a.val+b.val+n by ring]
  field_simp

/-- Shifted Beta moments retain cases whose unshifted first parameter is not integrable. -/
theorem integral_betaWeight_mul_powOn (a b : BetaParameter) (n : ℕ) :
    Integrable (fun t : Ioo (0 : ℝ) 1 ↦
      ((t.val : ℂ) ^ (a.val - n - 1) * (1 - (t.val : ℂ)) ^ (b.val - 1)) *
        (t.val : ℂ) ^ n) (Measure.comap Subtype.val volume) ∧
    (∫ t : Ioo (0 : ℝ) 1,
      ((t.val : ℂ) ^ (a.val - n - 1) * (1 - (t.val : ℂ)) ^ (b.val - 1)) *
        (t.val : ℂ) ^ n ∂Measure.comap Subtype.val volume) = betaIntegralOn a b := by
  have he : (fun t : Ioo (0 : ℝ) 1 ↦
      ((t.val : ℂ) ^ (a.val - n - 1) * (1 - (t.val : ℂ)) ^ (b.val - 1)) *
        (t.val : ℂ) ^ n) =
      (fun t : Ioo (0 : ℝ) 1 ↦ (t.val : ℂ) ^ (a.val - 1) *
        (1 - (t.val : ℂ)) ^ (b.val - 1)) := by
    funext t
    have ht : (t.val : ℂ) ≠ 0 := ofReal_ne_zero.mpr t.property.1.ne'
    rw [mul_right_comm, ← cpow_natCast, ← cpow_add _ _ ht]
    congr 2
    ring
  rw [he]
  exact ⟨integrable_betaIntegralOn a b, rfl⟩
end Complex

namespace Complex

private theorem continuousOn_inv_eulerFactor (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ContinuousOn (fun t : ℝ ↦ ((1 - z * (t : ℂ)) ^ a)⁻¹) (Icc (0 : ℝ) 1) := by
  intro t ht
  have ht1 : ‖(t : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg ht.1] using ht.2
  have hzt : ‖z * (t : ℂ)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg z) ht1).trans_lt hz
  have hp : 0 < (1 - z * (t : ℂ)).re := by
    rw [sub_re, one_re]
    linarith [re_le_norm (z * (t : ℂ))]
  have hs : 1 - z * (t : ℂ) ∈ slitPlane := Or.inl hp
  have hc : ContinuousAt (fun s : ℝ ↦ 1 - z * (s : ℂ)) t := by fun_prop
  exact (((continuousAt_cpow_const (b := a) hs).comp (f := fun s : ℝ ↦ 1 - z * (s : ℂ)) hc).inv₀
    (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hs)))).continuousWithinAt

/-- A convergent binomial factor preserves every integrable weight. -/
theorem intervalIntegrable_div_eulerFactor (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    {w : ℝ → ℂ} (hw : IntervalIntegrable w volume 0 1) :
    IntervalIntegrable (fun t ↦ w t / (1 - z * (t : ℂ)) ^ a) volume 0 1 := by
  simpa only [div_eq_mul_inv] using hw.mul_continuousOn
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      continuousOn_inv_eulerFactor a hz)

private theorem integral_open_unit_eq_interval (f : ℝ → ℂ)
    (_hf : IntervalIntegrable f volume 0 1) :
    (∫ t : Ioo (0 : ℝ) 1, f t.val ∂Measure.comap Subtype.val volume) =
      ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  exact integral_subtype_comap (s := Ioo (0 : ℝ) 1) measurableSet_Ioo f

/-- The weighted binomial integral asserts integrability together with its sum. -/
theorem hasSum_integral_binomialOn (a : ℂ) (z : Metric.ball (0 : ℂ) 1)
    (w : Lp ℂ 1 (volume.restrict (Ioo (0 : ℝ) 1))) :
    (∀ n : ℕ, Integrable (fun t : Ioo (0 : ℝ) 1 ↦
      w t.val * (((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a) *
        (z.val * (t.val : ℂ)) ^ n)) (Measure.comap Subtype.val volume)) ∧
    Integrable (fun t : Ioo (0 : ℝ) 1 ↦ w t.val / (1 - z.val * (t.val : ℂ)) ^ a)
      (Measure.comap Subtype.val volume) ∧
    HasSum (fun n : ℕ ↦ ∫ t : Ioo (0 : ℝ) 1,
      w t.val * (((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a) *
        (z.val * (t.val : ℂ)) ^ n) ∂Measure.comap Subtype.val volume)
      (∫ t : Ioo (0 : ℝ) 1, w t.val / (1 - z.val * (t.val : ℂ)) ^ a
        ∂Measure.comap Subtype.val volume) := by
  have hz : ‖z.val‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using z.property
  have hw : IntervalIntegrable (fun t ↦ w t) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (memLp_one_iff_integrable.mp (Lp.memLp w))
  have hi (n : ℕ) : IntervalIntegrable (fun t : ℝ ↦
      w t * (((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a) *
        (z.val * (t : ℂ)) ^ n)) volume 0 1 := hw.mul_continuousOn (by fun_prop)
  have hj := intervalIntegrable_div_eulerFactor a hz hw
  refine ⟨fun n ↦ ?_, ?_, ?_⟩
  · have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp (hi n)
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp h
  · have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hj
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp h
  · convert hasSum_integral_binomial a hz hw using 1
    · funext n
      exact integral_open_unit_eq_interval _ (hi n)
    · exact integral_open_unit_eq_interval _ hj
end Complex
namespace Complex
open Polynomial
/-- Positive Euler parameters certify the Gauss denominator. -/
def eulerGaussParameters (a : ℂ) (b d : BetaParameter) : GaussParameters ℂ :=
  .ofNoPole a b.val (b.val + d.val)
    (GammaPoint.ofRePos _ (by simpa only [add_re] using add_pos b.property d.property)).property

/-- The Euler coefficient moment uses the admissible Gauss coefficient. -/
theorem integral_eulerHypergeometric_termOn (a : ℂ) (b d : BetaParameter) (n : ℕ) :
    Integrable (fun t : Ioo (0 : ℝ) 1 ↦
      ((n.factorial : ℂ)⁻¹*(ascPochhammer ℂ n).eval a) *
        (((t.val : ℂ)^(b.val-1)*(1-(t.val : ℂ))^(d.val-1))*(t.val : ℂ)^n))
      (Measure.comap Subtype.val volume) ∧
    (∫ t : Ioo (0 : ℝ) 1,
      ((n.factorial : ℂ)⁻¹*(ascPochhammer ℂ n).eval a) *
        (((t.val : ℂ)^(b.val-1)*(1-(t.val : ℂ))^(d.val-1))*(t.val : ℂ)^n)
      ∂Measure.comap Subtype.val volume) =
      betaIntegralOn b d * ordinaryHypergeometricCoefficientOn (eulerGaussParameters a b d) n := by
  let bn : BetaParameter := ⟨b.val+n, by
    simp only [add_re,natCast_re]
    exact add_pos_of_pos_of_nonneg b.property (Nat.cast_nonneg _)⟩
  have h := integral_betaWeight_mul_powOn bn d n
  have he : bn.val-n-1 = b.val-1 := by dsimp only [bn]; ring
  simp only [he] at h
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul, h.2]
  have hcn : (ascPochhammer ℂ n).eval (eulerGaussParameters a b d).c ≠ 0 := by
    intro hz
    obtain ⟨k,_,hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp hz
    have hr := congrArg Complex.re hk
    simp only [eulerGaussParameters, GaussParameters.ofNoPole, natCast_re, neg_re, add_re] at hr
    linarith [b.property, d.property, Nat.cast_nonneg (α := ℝ) k]
  rw [betaIntegralOn_add_nat_left, ordinaryHypergeometricCoefficientOn_eq_div _ n hcn]
  dsimp only [eulerGaussParameters,GaussParameters.ofNoPole]
  ring

/-- Euler's integral together with its integrability, on the classical domain. -/
theorem integral_eulerHypergeometricOn (a : ℂ) (b d : BetaParameter)
    (z : Metric.ball (0 : ℂ) 1) :
    Integrable (fun t : Ioo (0 : ℝ) 1 ↦
      ((t.val : ℂ)^(b.val-1)*(1-(t.val : ℂ))^(d.val-1)) /
        (1-z.val*(t.val : ℂ))^a) (Measure.comap Subtype.val volume) ∧
    (∫ t : Ioo (0 : ℝ) 1,
      ((t.val : ℂ)^(b.val-1)*(1-(t.val : ℂ))^(d.val-1)) /
        (1-z.val*(t.val : ℂ))^a ∂Measure.comap Subtype.val volume) =
      betaIntegralOn b d * ordinaryHypergeometricOn (eulerGaussParameters a b d)
        (.ofUnitDisk _ z) := by
  let W : ℝ → ℂ := fun t ↦ if h : t ∈ Ioo (0 : ℝ) 1 then
    (t : ℂ)^(b.val-1)*(1-(t : ℂ))^(d.val-1) else 0
  have hW (t : Ioo (0 : ℝ) 1) : W t.val =
      (t.val : ℂ)^(b.val-1)*(1-(t.val : ℂ))^(d.val-1) := by
    simp only [W,dite_eq_left t.property]
  have hiW : IntegrableOn W (Ioo (0 : ℝ) 1) volume := by
    apply (integrableOn_iff_comap_subtypeVal (f := W) (μ := volume) measurableSet_Ioo).mpr
    apply (integrable_betaIntegralOn b d).congr
    filter_upwards [] with t
    exact (hW t).symm
  let w := (memLp_one_iff_integrable.mpr hiW).toLp W
  have hew : (fun t : Ioo (0 : ℝ) 1 ↦ w t.val) =ᵐ[Measure.comap Subtype.val volume]
      (fun t ↦ (t.val : ℂ)^(b.val-1)*(1-(t.val : ℂ))^(d.val-1)) := by
    have hw := (ae_restrict_iff_subtype measurableSet_Ioo).mp
      (memLp_one_iff_integrable.mpr hiW).coeFn_toLp
    filter_upwards [hw] with t ht
    exact ht.trans (hW t)
  obtain ⟨hterms,hint,hsum⟩ := hasSum_integral_binomialOn a z w
  have heval : (∫ t : Ioo (0 : ℝ) 1, w t.val / (1-z.val*(t.val : ℂ))^a
      ∂Measure.comap Subtype.val volume) =
      (∫ t : Ioo (0 : ℝ) 1,
      ((t.val : ℂ)^(b.val-1)*(1-(t.val : ℂ))^(d.val-1)) /
        (1-z.val*(t.val : ℂ))^a ∂Measure.comap Subtype.val volume) := by
    apply integral_congr_ae
    filter_upwards [hew] with t ht
    rw [ht]
  refine ⟨hint.congr ?_, ?_⟩
  · filter_upwards [hew] with t ht
    rw [ht]
  · have hterm (n : ℕ) : (∫ t : Ioo (0 : ℝ) 1,
        w t.val * (((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a) *
          (z.val * (t.val : ℂ)) ^ n) ∂Measure.comap Subtype.val volume) =
        betaIntegralOn b d * (ordinaryHypergeometricCoefficientOn (eulerGaussParameters a b d) n * z.val^n) := by
      calc
        _ = (∫ t : Ioo (0 : ℝ) 1,
            (((n.factorial : ℂ)⁻¹*(ascPochhammer ℂ n).eval a) *
            (((t.val : ℂ)^(b.val-1)*(1-(t.val : ℂ))^(d.val-1))*(t.val : ℂ)^n)) * z.val^n
            ∂Measure.comap Subtype.val volume) := by
          apply integral_congr_ae
          filter_upwards [hew] with t ht
          rw [ht,mul_pow]
          ring
        _ = _ := by rw [integral_mul_const,(integral_eulerHypergeometric_termOn a b d n).2,mul_assoc]
    simp_rw [hterm] at hsum
    rw [heval] at hsum
    exact hsum.unique ((hasSum_ordinaryHypergeometricOn (eulerGaussParameters a b d) z).mul_left _)
end Complex
namespace Complex
/-- Euler's classical integral in regularized normalization. -/
theorem integral_eulerRegularizedHypergeometricOn (a : ℂ) (b d : BetaParameter)
    (z : Metric.ball (0 : ℂ) 1) :
    let c := GammaPoint.ofRePos (b.val+d.val)
      (by simpa only [add_re] using add_pos b.property d.property)
    (∫ t : Ioo (0 : ℝ) 1,
      ((t.val : ℂ)^(b.val-1)*(1-(t.val : ℂ))^(d.val-1)) /
        (1-z.val*(t.val : ℂ))^a ∂Measure.comap Subtype.val volume) =
      GammaOn (.ofRePos b.val b.property) * GammaOn (.ofRePos d.val d.property) *
        regularizedGaussHGFunOn a b.val c.val
          (.ofGauss a b.val c (.ofUnitDisk (eulerGaussParameters a b d) z)) := by
  dsimp only
  rw [(integral_eulerHypergeometricOn a b d z).2, betaIntegralOn_eq_Gamma]
  dsimp only [eulerGaussParameters]
  erw [← ordinaryHypergeometricOn_div_Gamma_eq]
  dsimp only [GammaPoint.ofRePos]
  ring

end Complex
namespace Real
/-- The real Euler parameters give an admissible classical Gauss series. -/
def eulerGaussParameters (a : ℝ) (b d : Ioi (0 : ℝ)) : GaussParameters ℝ :=
  .ofNoPole a b.val (b.val+d.val) (GammaPoint.ofPos _ (add_pos b.property d.property)).property

/-- The real Euler integral has its actual integrability and classical value. -/
theorem integral_eulerHypergeometricOn (a : ℝ) (b d : Ioi (0 : ℝ))
    (z : Metric.ball (0 : ℝ) 1) :
    Integrable (fun t : Ioo (0 : ℝ) 1 ↦
      t.val^(b.val-1)*(1-t.val)^(d.val-1)/(1-z.val*t.val)^a)
      (Measure.comap Subtype.val volume) ∧
    (∫ t : Ioo (0 : ℝ) 1,
      t.val^(b.val-1)*(1-t.val)^(d.val-1)/(1-z.val*t.val)^a
      ∂Measure.comap Subtype.val volume) =
      (GammaOn (.ofPos b.val b.property) * GammaOn (.ofPos d.val d.property) /
        GammaOn (.ofPos (b.val+d.val) (add_pos b.property d.property))) *
        ordinaryHypergeometricOn (eulerGaussParameters a b d) (.ofUnitDisk _ z) := by
  have hz : |z.val| < 1 := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using z.property
  let bc : Complex.BetaParameter := ⟨(b.val : ℂ), b.property⟩
  let dc : Complex.BetaParameter := ⟨(d.val : ℂ), d.property⟩
  let zc : Metric.ball (0 : ℂ) 1 := ⟨(z.val : ℂ), by simpa using hz⟩
  have he (t : Ioo (0 : ℝ) 1) :
      ((t.val : ℂ)^(bc.val-1)*(1-(t.val : ℂ))^(dc.val-1)) /
        (1-zc.val*(t.val : ℂ))^(a : ℂ) =
      ((t.val^(b.val-1)*(1-t.val)^(d.val-1)/(1-z.val*t.val)^a : ℝ) : ℂ) := by
    have hp : 0 < 1-z.val*t.val := by
      have h₁ := mul_le_mul_of_nonneg_right (le_abs_self z.val) t.property.1.le
      have h₂ := (mul_le_of_le_one_right (abs_nonneg z.val) t.property.2.le).trans_lt hz
      linarith
    dsimp [bc, dc, zc]
    rw [Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_cpow t.property.1.le,
      Complex.ofReal_cpow (by linarith [t.property.2] : 0 ≤ 1-t.val),
      Complex.ofReal_cpow hp.le]
    push_cast
    rfl
  have hc := (Complex.integral_eulerHypergeometricOn (a : ℂ) bc dc zc).1
  have hi : Integrable (fun t : Ioo (0 : ℝ) 1 ↦
      t.val^(b.val-1)*(1-t.val)^(d.val-1)/(1-z.val*t.val)^a)
      (Measure.comap Subtype.val volume) := by
    have h := Complex.reCLM.integrable_comp hc
    simpa only [he, Complex.reCLM_apply, Complex.ofReal_re] using h
  refine ⟨hi, ?_⟩
  have hp : (eulerGaussParameters a b d).toComplex =
      Complex.eulerGaussParameters (a : ℂ) bc dc := by
    simp only [eulerGaussParameters,GaussParameters.toComplex,
      Complex.eulerGaussParameters,GaussParameters.ofNoPole,bc,dc,Complex.ofReal_add]
  have hv : ((ordinaryHypergeometricOn (eulerGaussParameters a b d) (.ofUnitDisk _ z) : ℝ) : ℂ) =
      ordinaryHypergeometricOn (Complex.eulerGaussParameters (a : ℂ) bc dc) (.ofUnitDisk _ zc) := by
    rw [Complex.ofReal_ordinaryHypergeometric]
    have hpoint : ((GaussSeriesPoint.ofUnitDisk (eulerGaussParameters a b d) z).toComplex
        (eulerGaussParameters a b d)).val = zc.val := rfl
    generalize hzz : (GaussSeriesPoint.ofUnitDisk (eulerGaussParameters a b d) z).toComplex
      (eulerGaussParameters a b d) = zz at *
    clear hzz
    revert zz
    rw [hp]
    intro zz hpoint
    congr 1
    exact Subtype.ext hpoint
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,hv]
  have hvalue := (Complex.integral_eulerHypergeometricOn (a : ℂ) bc dc zc).2
  rw [Complex.betaIntegralOn_eq_Gamma] at hvalue
  calc
    _ = (∫ t : Ioo (0 : ℝ) 1,
      ((t.val : ℂ)^(bc.val-1)*(1-(t.val : ℂ))^(dc.val-1)) /
        (1-zc.val*(t.val : ℂ))^(a : ℂ) ∂Measure.comap Subtype.val volume) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [] with t
      exact (he t).symm
    _ = _ := by
      rw [hvalue]
      simp only [Complex.GammaOn,Complex.GammaPoint.ofRePos,GammaOn,GammaPoint.ofPos,
        bc,dc,← Complex.ofReal_add,Complex.Gamma_ofReal,Complex.ofReal_div,Complex.ofReal_mul]
end Real
