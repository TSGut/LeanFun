/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.PolynomialVolterra
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-! # Uniqueness for polynomial first-kind Volterra equations

Differentiation reduces the homogeneous equation to a second-kind equation.
A continuous representative and Grönwall give uniqueness for integrable inputs
on a finite interval. The diagonal may have either sign. This supplies the
injectivity argument required in Gutleb's thesis, §2.7; it does not identify
raw Jacobi coefficient spaces with physical function spaces.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- The homogeneous Volterra integral inequality forces a continuous function to vanish. -/
theorem Real.eq_zero_of_norm_le_volterra_integral {f : ℝ → ℝ} {b M : ℝ}
    (hf : Continuous f)
    (hbound : ∀ x ∈ Icc 0 b, ‖f x‖ ≤ M * ∫ y in (0 : ℝ)..x, ‖f y‖) :
    ∀ x ∈ Icc 0 b, f x = 0 := by
  have hi (a c : ℝ) : IntervalIntegrable (fun y ↦ ‖f y‖) volume a c :=
    hf.norm.intervalIntegrable a c
  have hF := intervalIntegral.continuous_primitive hi 0
  have hd (x : ℝ) : HasDerivAt (fun x ↦ ∫ y in (0 : ℝ)..x, ‖f y‖) ‖f x‖ x :=
    intervalIntegral.integral_hasDerivAt_right (hi 0 x)
      hf.norm.stronglyMeasurable.stronglyMeasurableAtFilter hf.norm.continuousAt
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (a := 0) (b := b)
    hF.continuousOn (fun x _ ↦ (hd x).hasDerivWithinAt)
    (by simp) (fun x hx ↦ (by
      rw [norm_norm]
      exact (hbound x ⟨hx.1, hx.2.le⟩).trans_eq (by
        rw [Real.norm_of_nonneg (intervalIntegral.integral_nonneg hx.1
          (fun y _ ↦ norm_nonneg (f y)))])))
  intro x hx
  have hh := hbound x hx
  rw [hz x hx, mul_zero] at hh
  exact norm_le_zero_iff.mp hh

namespace MvPolynomial

/-- Polynomial multiplication preserves integrability on each subinterval. -/
theorem intervalIntegrable_polynomialKernel_mul_on (K : MvPolynomial (Fin 2) ℝ)
    {f : ℝ → ℝ} {b : ℝ} (hf : IntegrableOn f (Icc 0 b)) (x : Icc (0 : ℝ) b) :
    IntervalIntegrable (fun y ↦ eval ![(x : ℝ),y] K * f y) volume 0 (x : ℝ) := by
  have hi : IntervalIntegrable f volume 0 (x : ℝ) := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le x.property.1]
    exact hf.mono_set (fun y hy ↦ ⟨hy.1.le, hy.2.trans x.property.2⟩)
  exact hi.continuousOn_mul ((K.continuous_eval.comp (by fun_prop)).continuousOn)

/-- Polynomial kernels with interval-integrable inputs supply every physical row. -/
def _root_.Real.VolterraIntegralInput.ofIntegrableOnPolynomial
    (K : MvPolynomial (Fin 2) ℝ) {f : ℝ → ℝ} {b : ℝ}
    (hf : IntegrableOn f (Icc 0 b)) (x : Icc (0 : ℝ) b) :
    Real.VolterraIntegralInput (x : ℝ) :=
  .ofKernel (fun z ↦ eval z K) f (intervalIntegrable_polynomialKernel_mul_on K hf x)

private theorem continuous_polynomialKernelIntegral_bridge
    (K : MvPolynomial (Fin 2) ℝ) (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) :
    Continuous (fun x ↦ ∫ y in (0 : ℝ)..x, eval ![x,y] K * f y) := by
  simpa only [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel] using
    continuous_polynomialVolterraIntegral K f hf

private theorem ae_hasDerivAt_polynomialKernelIntegral_bridge
    (K : MvPolynomial (Fin 2) ℝ) (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, HasDerivAt (fun t ↦ ∫ y in (0 : ℝ)..t, eval ![t,y] K * f y)
      (eval (fun _ ↦ x) K * f x + ∫ y in (0 : ℝ)..x, eval ![x,y] (pderiv 0 K) * f y) x := by
  simpa only [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel] using
    ae_hasDerivAt_polynomialVolterraIntegral K f hf

/-- A zero first-kind output satisfies the differentiated homogeneous equation almost everywhere. -/
private theorem ae_diagonal_mul_eq_neg_polynomialVolterraIntegral_integral {K : MvPolynomial (Fin 2) ℝ}
    {f : ℝ → ℝ} {b : ℝ} (hf : LocallyIntegrable f volume)
    (hz : ∀ x ∈ Icc 0 b, (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y) x = 0) :
    ∀ᵐ x ∂volume.restrict (Icc 0 b),
      eval (fun _ ↦ x) K * f x = -(fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (pderiv 0 K) * f y) x := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
  filter_upwards [ae_restrict_of_ae (ae_hasDerivAt_polynomialKernelIntegral_bridge K f hf),
    self_mem_ae_restrict measurableSet_Ioo] with x hx hxi
  have he : (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y) =ᶠ[𝓝 x] fun _ ↦ 0 :=
    Filter.Eventually.mono (isOpen_Ioo.mem_nhds hxi) (fun y hy ↦ hz y ⟨hy.1.le, hy.2.le⟩)
  have hd : HasDerivAt ((fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y)) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
  exact eq_neg_of_add_eq_zero_left (hx.unique hd)

/-- A continuous input with zero output and a nonvanishing kernel diagonal vanishes. -/
private theorem eq_zero_of_polynomialVolterraIntegral_eq_zero_integral {K : MvPolynomial (Fin 2) ℝ}
    {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (hf : Continuous f)
    (hdiag : ∀ x ∈ Icc 0 b, eval (fun _ ↦ x) K ≠ 0)
    (hz : ∀ x ∈ Icc 0 b, (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y) x = 0) :
    ∀ x ∈ Icc 0 b, f x = 0 := by
  have hdc : Continuous (fun x : ℝ ↦ eval (fun _ ↦ x) K) :=
    K.continuous_eval.comp (by fun_prop)
  have hd := ae_diagonal_mul_eq_neg_polynomialVolterraIntegral_integral hf.locallyIntegrable hz
  have hid := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hb) hd
    (hdc.mul hf).continuousOn
    (continuous_polynomialKernelIntegral_bridge (pderiv 0 K) f hf.locallyIntegrable).neg.continuousOn
  let q : ℝ × ℝ → ℝ := fun z ↦
    eval (![z.1, z.2] : Fin 2 → ℝ) (pderiv 0 K) / eval (fun _ ↦ z.1) K
  have hq : ContinuousOn q (Icc 0 b ×ˢ Icc 0 b) :=
    ((pderiv 0 K).continuous_eval.comp (by fun_prop)).continuousOn.div
      (hdc.comp continuous_fst).continuousOn (fun z hz ↦ hdiag z.1 hz.1)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hq
  apply Real.eq_zero_of_norm_le_volterra_integral hf
  intro x hx
  have he : f x = -(∫ y in (0 : ℝ)..x, q (x, y) * f y) := by
    have hi : (∫ y in (0 : ℝ)..x, q (x, y) * f y) =
        (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (pderiv 0 K) * f y) x / eval (fun _ ↦ x) K := by
      simp only [q, div_mul_eq_mul_div]
      exact intervalIntegral.integral_div _ _
    rw [hi, ← neg_div]
    apply (eq_div_iff (hdiag x hx)).mpr
    simpa only [mul_comm] using hid hx
  have hkc : Continuous (fun y : ℝ ↦ eval (![x, y] : Fin 2 → ℝ) (pderiv 0 K)) :=
    (pderiv 0 K).continuous_eval.comp (by fun_prop)
  have hc : Continuous (fun y ↦ q (x, y) * f y) :=
    (hkc.div_const (eval (fun _ ↦ x) K)).mul hf
  calc
    ‖f x‖ = ‖∫ y in (0 : ℝ)..x, q (x, y) * f y‖ := by rw [he, norm_neg]
    _ ≤ ∫ y in (0 : ℝ)..x, ‖q (x, y) * f y‖ :=
      intervalIntegral.norm_integral_le_integral_norm hx.1
    _ ≤ ∫ y in (0 : ℝ)..x, M * ‖f y‖ :=
      intervalIntegral.integral_mono_on hx.1 (hc.norm.intervalIntegrable _ _)
        ((hf.norm.const_mul M).intervalIntegrable _ _) (fun y hy ↦ by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hM (x,y) ⟨hx, hy.1, hy.2.trans hx.2⟩)
            (norm_nonneg _))
    _ = M * ∫ y in (0 : ℝ)..x, ‖f y‖ := intervalIntegral.integral_const_mul _ _

/-- Volterra integration on a subinterval depends only on the almost-everywhere input class. -/
private theorem polynomialVolterraIntegral_congr_ae_on_integral (K : MvPolynomial (Fin 2) ℝ)
    {f g : ℝ → ℝ} {b x : ℝ} (hx : x ∈ Icc 0 b)
    (hfg : f =ᵐ[volume.restrict (Icc 0 b)] g)
    (_hf : IntervalIntegrable (fun y ↦ eval ![x,y] K * f y) volume 0 x)
    (_hg : IntervalIntegrable (fun y ↦ eval ![x,y] K * g y) volume 0 x) :
    (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y) x = (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * g y) x := by
  apply intervalIntegral.integral_congr_ae_restrict
  have hs : Set.uIoc 0 x ⊆ Icc 0 b := by
    rw [uIoc_of_le hx.1]
    exact fun y hy ↦ ⟨hy.1.le, hy.2.trans hx.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hfg] with y hy
  rw [hy]

/-- A locally integrable input with zero output vanishes almost everywhere on the interval. -/
private theorem ae_eq_zero_of_polynomialVolterraIntegral_eq_zero_integral {K : MvPolynomial (Fin 2) ℝ}
    {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (hf : LocallyIntegrable f volume)
    (hdiag : ∀ x ∈ Icc 0 b, eval (fun _ ↦ x) K ≠ 0)
    (hz : ∀ x ∈ Icc 0 b, (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y) x = 0) :
    f =ᵐ[volume.restrict (Icc 0 b)] 0 := by
  let c : ℝ → ℝ := fun x ↦ max 0 (min b x)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcm (x : ℝ) : c x ∈ Icc 0 b :=
    ⟨le_max_left _ _, max_le hb.le (min_le_left _ _)⟩
  have hce (x : ℝ) (hx : x ∈ Icc 0 b) : c x = x := by
    simp only [c, min_eq_right hx.2, max_eq_right hx.1]
  let g : ℝ → ℝ := fun x ↦
    -(fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (pderiv 0 K) * f y) (c x) / eval (fun _ ↦ c x) K
  have hg : Continuous g :=
    ((continuous_polynomialKernelIntegral_bridge (pderiv 0 K) f hf).comp hc).neg.div
      (K.continuous_eval.comp (by fun_prop)) (fun x ↦ hdiag _ (hcm x))
  have hfg : f =ᵐ[volume.restrict (Icc 0 b)] g := by
    filter_upwards [ae_diagonal_mul_eq_neg_polynomialVolterraIntegral_integral hf hz,
      self_mem_ae_restrict measurableSet_Icc] with x hx hxi
    change f x = -(fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) (pderiv 0 K) * f y) (c x) / eval (fun _ ↦ c x) K
    rw [hce x hxi]
    apply (eq_div_iff (hdiag x hxi)).mpr
    simpa only [mul_comm] using hx
  have hgz : ∀ x ∈ Icc 0 b, (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * g y) x = 0 := by
    intro x hx
    rw [← polynomialVolterraIntegral_congr_ae_on_integral K hx hfg
      (intervalIntegrable_polynomialKernel_mul K hf x 0 x)
      (intervalIntegrable_polynomialKernel_mul K hg.locallyIntegrable x 0 x)]
    exact hz x hx
  have hg0 := eq_zero_of_polynomialVolterraIntegral_eq_zero_integral hb hg hdiag hgz
  filter_upwards [hfg, self_mem_ae_restrict measurableSet_Icc] with x hx hxi
  exact hx.trans (hg0 x hxi)

/-- First-kind uniqueness requires only integrability on the interval, not global regularity. -/
private theorem ae_eq_zero_of_integrableOn_polynomialVolterraIntegral_eq_zero_integral
    {K : MvPolynomial (Fin 2) ℝ} {f : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hf : IntegrableOn f (Icc 0 b))
    (hdiag : ∀ x ∈ Icc 0 b, eval (fun _ ↦ x) K ≠ 0)
    (hz : ∀ x ∈ Icc 0 b, (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * f y) x = 0) :
    f =ᵐ[volume.restrict (Icc 0 b)] 0 := by
  let g := (Icc 0 b).indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Icc
  have hgf : g =ᵐ[volume.restrict (Icc 0 b)] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    exact indicator_of_mem hx f
  have hgz : ∀ x ∈ Icc 0 b, (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, eval (![x, y] : Fin 2 → ℝ) K * g y) x = 0 := by
    intro x hx
    rw [polynomialVolterraIntegral_congr_ae_on_integral K hx hgf
      (intervalIntegrable_polynomialKernel_mul K hg.locallyIntegrable x 0 x)
      (intervalIntegrable_polynomialKernel_mul_on K hf ⟨x,hx⟩)]
    exact hz x hx
  exact hgf.symm.trans (ae_eq_zero_of_polynomialVolterraIntegral_eq_zero_integral hb hg.locallyIntegrable hdiag hgz)

/-- A zero classical output satisfies the differentiated homogeneous equation. -/
theorem ae_diagonal_mul_eq_neg_polynomialVolterraIntegral {K : MvPolynomial (Fin 2) ℝ}
    {f : ℝ → ℝ} {b : ℝ} (hf : LocallyIntegrable f volume)
    (hz : ∀ x ∈ Icc 0 b, Real.volterraIntegral (.ofPolynomial K hf x) = 0) :
    ∀ᵐ x ∂volume.restrict (Icc 0 b), eval (fun _ ↦ x) K * f x =
      -Real.volterraIntegral (.ofPolynomial (pderiv 0 K) hf x) := by
  simp only [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel] at hz ⊢
  exact ae_diagonal_mul_eq_neg_polynomialVolterraIntegral_integral hf hz

/-- A continuous input with zero output and a nonzero diagonal vanishes. -/
theorem eq_zero_of_polynomialVolterraIntegral_eq_zero {K : MvPolynomial (Fin 2) ℝ}
    {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (hf : Continuous f)
    (hdiag : ∀ x ∈ Icc 0 b, eval (fun _ ↦ x) K ≠ 0)
    (hz : ∀ x ∈ Icc 0 b, Real.volterraIntegral (.ofPolynomial K hf.locallyIntegrable x) = 0) :
    ∀ x ∈ Icc 0 b, f x = 0 := by
  simp only [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel] at hz
  exact eq_zero_of_polynomialVolterraIntegral_eq_zero_integral hb hf hdiag hz

/-- Almost-everywhere equal inputs have the same existing polynomial row integral. -/
theorem polynomialVolterraIntegral_congr_ae_on (K : MvPolynomial (Fin 2) ℝ)
    {f g : ℝ → ℝ} {b : ℝ} (x : Icc (0 : ℝ) b)
    (hfg : f =ᵐ[volume.restrict (Icc 0 b)] g)
    (hf : IntervalIntegrable (fun y ↦ eval ![(x : ℝ),y] K * f y) volume 0 (x : ℝ))
    (hg : IntervalIntegrable (fun y ↦ eval ![(x : ℝ),y] K * g y) volume 0 (x : ℝ)) :
    Real.volterraIntegral (.ofKernel (fun z ↦ eval z K) f hf) =
      Real.volterraIntegral (.ofKernel (fun z ↦ eval z K) g hg) := by
  simp only [Real.volterraIntegral_ofKernel]
  exact polynomialVolterraIntegral_congr_ae_on_integral K x.property hfg hf hg

/-- Locally integrable data with zero output vanish almost everywhere. -/
theorem ae_eq_zero_of_polynomialVolterraIntegral_eq_zero {K : MvPolynomial (Fin 2) ℝ}
    {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (hf : LocallyIntegrable f volume)
    (hdiag : ∀ x ∈ Icc 0 b, eval (fun _ ↦ x) K ≠ 0)
    (hz : ∀ x ∈ Icc 0 b, Real.volterraIntegral (.ofPolynomial K hf x) = 0) :
    f =ᵐ[volume.restrict (Icc 0 b)] 0 := by
  simp only [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel] at hz
  exact ae_eq_zero_of_polynomialVolterraIntegral_eq_zero_integral hb hf hdiag hz

/-- First-kind uniqueness requires only integrability on the physical interval. -/
theorem ae_eq_zero_of_integrableOn_polynomialVolterraIntegral_eq_zero
    {K : MvPolynomial (Fin 2) ℝ} {f : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hf : IntegrableOn f (Icc 0 b))
    (hdiag : ∀ x ∈ Icc 0 b, eval (fun _ ↦ x) K ≠ 0)
    (hz : ∀ x : Icc (0 : ℝ) b,
      Real.volterraIntegral (.ofIntegrableOnPolynomial K hf x) = 0) :
    f =ᵐ[volume.restrict (Icc 0 b)] 0 := by
  apply ae_eq_zero_of_integrableOn_polynomialVolterraIntegral_eq_zero_integral hb hf hdiag
  intro x hx
  simpa only [Real.VolterraIntegralInput.ofIntegrableOnPolynomial,
    Real.volterraIntegral_ofKernel] using hz ⟨x,hx⟩

end MvPolynomial
