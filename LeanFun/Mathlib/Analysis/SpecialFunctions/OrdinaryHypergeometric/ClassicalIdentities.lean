/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.ODE.SecondOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.LinearCombination
public import Mathlib.Analysis.Analytic.Binomial
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.ClassicalAnalytic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain
@[expose] public noncomputable section
open Polynomial Set
namespace Real
/-- Cancellation of a non-pole denominator on the open unit disk. -/
theorem ordinaryHypergeometricOn_cancel (a : ℝ) (c : GammaPoint)
    (z : Metric.ball (0 : ℝ) 1) :
    ordinaryHypergeometricOn (.ofNoPole a c.val c.val c.property)
      (.ofUnitDisk _ z) = (1-z.val)^(-a) := by
  have hz : |z.val| < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using z.property
  have hc (n : ℕ) : (ascPochhammer ℝ n).eval c.val ≠ 0 := by
    intro hn
    obtain ⟨k,_,hk⟩ := (ascPochhammer_eval_eq_zero_iff n c.val).mp hn
    exact c.property k (by simpa using congrArg Neg.neg hk.symm)
  have h := (one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum
    (y := z.val) (by
      rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
      exact_mod_cast hz)
  have hcoeff (n : ℕ) : Ring.choose (a+n-1) n =
      (n.factorial : ℝ)⁻¹ * (ascPochhammer ℝ n).eval a := by
    rw [← Ring.multichoose_eq]
    have hn := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
    simp only [nsmul_eq_mul, ascPochhammer_smeval_eq_eval] at hn
    have hne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    apply mul_left_cancel₀ hne
    rw [hn, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    hcoeff, zero_add] at h
  have he (n : ℕ) : ordinaryHypergeometricCoefficientOn
      (.ofNoPole a c.val c.val c.property) n =
      (n.factorial : ℝ)⁻¹ * (ascPochhammer ℝ n).eval a := by
    rw [ordinaryHypergeometricCoefficientOn_eq_div _ n (hc n)]
    dsimp only [GaussParameters.ofNoPole]
    have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp [hc n, hf]
  have hs := hasSum_ordinaryHypergeometricOn (.ofNoPole a c.val c.val c.property) z
  simp only [he] at hs
  have hv := hs.unique h
  rw [rpow_neg (by linarith [le_abs_self z.val] : 0 ≤ 1-z.val)]
  simpa only [one_div] using hv

/-- Positive equal parameters are a special case of cancellation. -/
theorem ordinaryHypergeometricOn_cancel_of_pos (a : ℝ) (c : Ioi (0 : ℝ))
    (z : Metric.ball (0 : ℝ) 1) :
    ordinaryHypergeometricOn (.ofNoPole a c.val c.val (GammaPoint.ofPos c.val c.property).property)
      (.ofUnitDisk _ z) = (1-z.val)^(-a) :=
  ordinaryHypergeometricOn_cancel a (.ofPos c.val c.property) z
end Real

namespace Real
private theorem nonpole_value (a b : ℝ) (c : GammaPoint) (z : Metric.ball (0 : ℝ) 1) :
    ordinaryHypergeometricOn (.ofNoPole a b c.val c.property) (.ofUnitDisk _ z) =
      ordinaryHypergeometric a b c.val z.val := by
  have hc (n : ℕ) : (ascPochhammer ℝ n).eval c.val ≠ 0 := by
    intro hn
    obtain ⟨k,_,hk⟩ := (ascPochhammer_eval_eq_zero_iff n c.val).mp hn
    exact c.property k (by simpa using congrArg Neg.neg hk.symm)
  have he (n : ℕ) : ordinaryHypergeometricCoefficientOn
      (.ofNoPole a b c.val c.property) n = ordinaryHypergeometricCoefficient a b c.val n := by
    rw [ordinaryHypergeometricCoefficientOn_eq_div _ n (hc n)]
    dsimp only [GaussParameters.ofNoPole, ordinaryHypergeometricCoefficient]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hs := hasSum_ordinaryHypergeometricOn (.ofNoPole a b c.val c.property) z
  simp only [he] at hs
  rw [ordinaryHypergeometric_eq_tsum]
  simpa only [ordinaryHypergeometricCoefficient, smul_eq_mul, mul_assoc] using hs.tsum_eq.symm
private theorem nonpole_analytic (a b : ℝ) (c : GammaPoint) {z : ℝ} (hz : ‖z‖ < 1) :
    AnalyticAt ℝ (ordinaryHypergeometric a b c.val) z := by
  let U : TopologicalSpace.Opens ℝ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  let p := GaussParameters.ofNoPole a b c.val c.property
  have hf (y : U) : ordinaryHypergeometric a b c.val y.val =
      ordinaryHypergeometricOn p (.ofUnitDisk p y) := (nonpole_value a b c y).symm
  exact ((analyticOnOpen_iff U _ (ordinaryHypergeometric a b c.val) hf).mp
    (analyticOnOpen_ordinaryHypergeometricOn p)) z
      (by change z ∈ Metric.ball (0 : ℝ) 1; simpa only [Metric.mem_ball, dist_zero_right] using hz)
private theorem nonpole_ode (a b : ℝ) (c : GammaPoint) {z : ℝ} (hz : ‖z‖ < 1) :
    z*(1-z)*deriv (deriv (ordinaryHypergeometric a b c.val)) z +
      (c.val-(a+b+1)*z)*deriv (ordinaryHypergeometric a b c.val) z -
        a*b*ordinaryHypergeometric a b c.val z = 0 := by
  let U : TopologicalSpace.Opens ℝ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  let p := GaussParameters.ofNoPole a b c.val c.property
  have hc (n : ℕ) : p.c+n ≠ 0 := by
    intro hn
    apply c.property n
    change c.val+n = 0 at hn
    exact eq_neg_of_add_eq_zero_left hn
  obtain ⟨d₁,d₂,hd⟩ := ordinaryHypergeometricOn_ode p hc
  have hf (y : U) : ordinaryHypergeometric a b c.val y.val =
      ordinaryHypergeometricOn p (.ofUnitDisk p y) := (nonpole_value a b c y).symm
  have h₁ (y : U) : HasDerivAt (ordinaryHypergeometric a b c.val) (d₁ y) y.val :=
    (hasDerivAtOnOpen_iff U _ (d₁ y) y (ordinaryHypergeometric a b c.val) hf).mp (hd y).1
  have he (y : U) : deriv (ordinaryHypergeometric a b c.val) y.val = d₁ y := (h₁ y).deriv
  let z₀ : U := ⟨z, by change z ∈ Metric.ball (0 : ℝ) 1; simpa only [Metric.mem_ball, dist_zero_right] using hz⟩
  have h₂ : HasDerivAt (deriv (ordinaryHypergeometric a b c.val)) (d₂ z₀) z :=
    (hasDerivAtOnOpen_iff U d₁ (d₂ z₀) z₀ (deriv (ordinaryHypergeometric a b c.val)) he).mp
      (hd z₀).2.1
  rw [(h₁ z₀).deriv, h₂.deriv, hf z₀]
  exact (hd z₀).2.2

private theorem norm_sq_lt_one {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : ‖x^2‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [hx.1, hx.2]

/-- First derivative of a Gauss function pulled back by squaring. -/
private theorem square_pullback_derivative (a b : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ ↦ ordinaryHypergeometric a b (1/2 : ℝ) (t^2))
      (2*x*deriv (ordinaryHypergeometric a b (1/2 : ℝ)) (x^2)) x := by
  have h := (nonpole_analytic a b (.ofPos (1/2) (by norm_num))
    (norm_sq_lt_one hx)).differentiableAt.hasDerivAt.comp (h := fun t : ℝ ↦ t^2) x ((hasDerivAt_id x).pow 2)
  simp only [GammaPoint.ofPos] at h
  convert h using 1
  · funext t
    rfl
  · dsimp
    ring

/-- The quadratic pullback has an ordinary, nonsingular second-order equation
on `(-1,1)`. This avoids a uniqueness argument at the Gauss equation's singular
point zero. -/
private theorem square_pullback_second (a b : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ ↦ 2*t*deriv (ordinaryHypergeometric a b (1/2 : ℝ)) (t^2))
      ((4*a*b*ordinaryHypergeometric a b (1/2 : ℝ) (x^2) +
        (2*a+2*b+1)*x*(2*x*deriv (ordinaryHypergeometric a b (1/2 : ℝ)) (x^2))) /
          (1-x^2)) x := by
  have hz := norm_sq_lt_one hx
  have hF := (nonpole_analytic a b (.ofPos (1/2) (by norm_num)) hz).deriv.differentiableAt.hasDerivAt
  have h := ((hasDerivAt_id x).const_mul 2).mul
    (hF.comp (h := fun t : ℝ ↦ t^2) x ((hasDerivAt_id x).pow 2))
  have he := nonpole_ode a b (.ofPos (1/2) (by norm_num)) hz
  have hn : 1-x^2 ≠ 0 := by nlinarith [hx.1, hx.2]
  simp only [GammaPoint.ofPos] at h he
  apply h.congr_deriv
  dsimp only [Function.comp_def, id_eq]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  apply (eq_div_iff hn).mpr
  linear_combination 4*he

private theorem norm_half_lt_one {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ‖(1+x)/2‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (by linarith [hx.1])]
  linarith [hx.2]

/-- First derivative for the affine pullback with its power prefactor. -/
private theorem affine_pullback_derivative (a p : ℝ) (hp : -1 < p) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ ↦ (1+t)^p * ordinaryHypergeometric a (1-a) (p+1) ((1+t)/2))
      (p*(1+x)^(p-1)*ordinaryHypergeometric a (1-a) (p+1) ((1+x)/2) +
        (1+x)^p/2 * deriv (ordinaryHypergeometric a (1-a) (p+1)) ((1+x)/2)) x := by
  have hS := (hasDerivAt_id x).const_add 1
  have hH := (nonpole_analytic a (1-a) (.ofPos (p+1) (by linarith))
    (norm_half_lt_one hx)).differentiableAt.hasDerivAt
  have hP := (hasDerivAt_rpow_const (p := p)
    (Or.inl (by linarith [hx.1] : 1+x ≠ 0))).comp x hS
  simp only [GammaPoint.ofPos] at hH
  convert hP.mul (hH.comp x (hS.div_const 2)) using 1
  · funext t
    rfl
  · dsimp
    ring

/-- The affine pullback with its power prefactor satisfies a symmetric
second-order equation on the interval. -/
private theorem affine_pullback_second (a p : ℝ)
    (hp : -1 < p) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ ↦
        p*(1+t)^(p-1)*ordinaryHypergeometric a (1-a) (p+1) ((1+t)/2) +
          (1+t)^p/2 * deriv (ordinaryHypergeometric a (1-a) (p+1)) ((1+t)/2))
      (((p*(p-1)+a*(1-a))*((1+x)^p * ordinaryHypergeometric a (1-a) (p+1) ((1+x)/2)) -
        (2*p-2)*x*(p*(1+x)^(p-1)*ordinaryHypergeometric a (1-a) (p+1) ((1+x)/2) +
          (1+x)^p/2 * deriv (ordinaryHypergeometric a (1-a) (p+1)) ((1+x)/2))) /
            (1-x^2)) x := by
  have hs : 0 < 1+x := by linarith [hx.1]
  have hn : 1-x^2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hS := (hasDerivAt_id x).const_add 1
  have hZ := hS.div_const 2
  have hH := nonpole_analytic a (1-a) (.ofPos (p+1) (by linarith)) (norm_half_lt_one hx)
  have hF := hH.differentiableAt.hasDerivAt.comp x hZ
  have hF₁ := hH.deriv.differentiableAt.hasDerivAt.comp x hZ
  have hP := (hasDerivAt_rpow_const (p := p) (Or.inl hs.ne')).comp x hS
  have hP₁ := (hasDerivAt_rpow_const (p := p-1) (Or.inl hs.ne')).comp x hS
  have h := ((hP₁.const_mul p).mul hF).add ((hP.div_const 2).mul hF₁)
  have he := nonpole_ode a (1-a) (.ofPos (p+1) (by linarith)) (norm_half_lt_one hx)
  have hs1 : (1+x)^(p-1) = (1+x)^(p-2)*(1+x) := by
    rw [← rpow_add_one hs.ne', show p-2+1 = p-1 by ring]
  have hs2 : (1+x)^p = (1+x)^(p-2)*(1+x)^2 := by
    rw [show (1+x)^2 = (1+x)^(2 : ℝ) by norm_cast, ← rpow_add hs]
    congr 1
    ring
  simp only [GammaPoint.ofPos] at h he
  apply h.congr_deriv
  dsimp only [Function.comp_def, id_eq]
  simp only [one_div, mul_one]
  apply (eq_div_iff hn).mpr
  rw [show p-1-1 = p-2 by ring, hs1, hs2]
  linear_combination ((1+x)^(p-2)*(1+x)^2)*he


/-- The even part of an affine Gauss pullback is a Gauss function of `x²`.
All arguments remain in the defining disks; numerator parameters are unrestricted. -/
private theorem even_quadratic_local (a p : ℝ) (hp : -1 < p) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (1+x)^p*ordinaryHypergeometric a (1-a) (p+1) ((1+x)/2) +
      (1-x)^p*ordinaryHypergeometric a (1-a) (p+1) ((1-x)/2) =
    2*ordinaryHypergeometric a (1-a) (p+1) (1/2 : ℝ) *
      ordinaryHypergeometric ((1-p-a)/2) ((a-p)/2) (1/2 : ℝ) (x^2) := by
  let F : ℝ → ℝ := fun t ↦ (1+t)^p*ordinaryHypergeometric a (1-a) (p+1) ((1+t)/2)
  let J : ℝ → ℝ := fun t ↦
    p*(1+t)^(p-1)*ordinaryHypergeometric a (1-a) (p+1) ((1+t)/2) +
      (1+t)^p/2*deriv (ordinaryHypergeometric a (1-a) (p+1)) ((1+t)/2)
  let c₀ := 2*ordinaryHypergeometric a (1-a) (p+1) (1/2 : ℝ)
  let u := (1-p-a)/2
  let v := (a-p)/2
  let G : ℝ → ℝ := fun t ↦ c₀*ordinaryHypergeometric u v (1/2 : ℝ) (t^2)
  let L : ℝ → ℝ := fun t ↦ c₀*(2*t*deriv (ordinaryHypergeometric u v (1/2 : ℝ)) (t^2))
  let A : ℝ → ℝ := fun t ↦ (p*(p-1)+a*(1-a))/(1-t^2)
  let B : ℝ → ℝ := fun t ↦ -(2*p-2)*t/(1-t^2)
  have hF (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) : HasDerivAt F (J t) t :=
    affine_pullback_derivative a p hp ht
  have hJ (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt J (A t*F t+B t*J t) t := by
    convert affine_pullback_second a p hp ht using 1
    dsimp only [A, B, F, J]
    ring
  have hG (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) : HasDerivAt G (L t) t :=
    (square_pullback_derivative u v ht).const_mul c₀
  have hL (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt L (A t*G t+B t*L t) t := by
    convert (square_pullback_second u v ht).const_mul c₀ using 1
    dsimp only [A, B, G, L, u, v]
    ring
  have hneg {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : -t ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hE (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun s ↦ F s+F (-s)) (J t-J (-t)) t := by
    convert (hF t ht).add ((hF (-t) (hneg ht)).comp t (hasDerivAt_neg t)) using 1
    · funext s
      rfl
    · ring
  have hE₁ (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun s ↦ J s-J (-s))
        (A t*(F t+F (-t))+B t*(J t-J (-t))) t := by
    convert (hJ t ht).sub ((hJ (-t) (hneg ht)).comp t (hasDerivAt_neg t)) using 1
    · funext s
      rfl
    · dsimp only [A, B]
      simp only [neg_sq]
      ring
  obtain ⟨r, hxr, hr⟩ := exists_between (abs_lt.mpr hx)
  have hr0 : 0 < r := (abs_nonneg x).trans_lt hxr
  have hsub : Icc (-r) r ⊆ Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hn (t : ℝ) (ht : t ∈ Icc (-r) r) : 1-t^2 ≠ 0 := by
    have hh := hsub ht
    nlinarith [hh.1, hh.2]
  have hA : ContinuousOn A (Icc (-r) r) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    exact hn
  have hB : ContinuousOn B (Icc (-r) r) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact hn
  have he := eqOn_of_secondOrder_linear_ode hA hB
    (t₀ := 0) (show (0 : ℝ) ∈ Ioo (-r) r by constructor <;> linarith)
    (fun t ht ↦ (hE t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hE₁ t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hG t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hL t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht ↦ hE t (hsub (Ioo_subset_Icc_self ht)))
    (fun t ht ↦ hE₁ t (hsub (Ioo_subset_Icc_self ht)))
    (fun t ht ↦ hG t (hsub (Ioo_subset_Icc_self ht)))
    (fun t ht ↦ hL t (hsub (Ioo_subset_Icc_self ht)))
    (by simp [F, G, c₀]; ring) (by simp [L])
  have hx' : x ∈ Icc (-r) r := ⟨(abs_lt.mp hxr).1.le, (abs_lt.mp hxr).2.le⟩
  simpa only [F, G, c₀, u, v, sub_eq_add_neg] using he hx'


/-- The even quadratic transformation, with all arguments in their classical domains. -/
theorem ordinaryHypergeometricOn_even_quadratic (a : ℝ) (p : Ioi (-1 : ℝ))
    (x : Ioo (-1 : ℝ) 1) :
    let q := GaussParameters.ofNoPole a (1-a) (p.val+1)
      (GammaPoint.ofPos _ (by linarith [show -1 < p.val from p.property])).property
    let r := GaussParameters.ofNoPole ((1-p.val-a)/2) ((a-p.val)/2) (1/2 : ℝ)
      (GammaPoint.ofPos _ (by norm_num)).property
    let zp : Metric.ball (0 : ℝ) 1 := ⟨(1+x.val)/2, by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [x.property.1, x.property.2]⟩
    let zm : Metric.ball (0 : ℝ) 1 := ⟨(1-x.val)/2, by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [x.property.1, x.property.2]⟩
    let zh : Metric.ball (0 : ℝ) 1 := ⟨1/2, by norm_num [Metric.mem_ball]⟩
    let zs : Metric.ball (0 : ℝ) 1 := ⟨x.val^2, by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [x.property.1, x.property.2]⟩
    (1+x.val)^p.val * ordinaryHypergeometricOn q (.ofUnitDisk q zp) +
      (1-x.val)^p.val * ordinaryHypergeometricOn q (.ofUnitDisk q zm) =
      2 * ordinaryHypergeometricOn q (.ofUnitDisk q zh) *
        ordinaryHypergeometricOn r (.ofUnitDisk r zs) := by
  dsimp only
  have hq := nonpole_value a (1-a)
    (.ofPos (p.val+1) (by linarith [show -1 < p.val from p.property]))
  have hr := nonpole_value ((1-p.val-a)/2) ((a-p.val)/2)
    (.ofPos (1/2) (by norm_num))
  simp only [GammaPoint.ofPos] at hq hr
  rw [hq, hq, hq, hr]
  exact even_quadratic_local a p.val p.property x.property

end Real
