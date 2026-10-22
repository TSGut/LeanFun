/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.PolynomialVolterra
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraApproximation
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Continuous Volterra primitives of integrable inputs

Uniform kernel approximation is uniform after applying the kernel to a fixed
integrable input. Reference: Linz (1985), basic Volterra integral estimates.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped Topology
namespace Real

/-- Continuous triangle kernels may be integrated against an integrable input on each slice. -/
theorem intervalIntegrable_continuousVolterra_mul
    {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
    {f : ℝ → ℝ} (hf : Integrable f volume) {x : ℝ} (hx : x ∈ Icc 0 1) :
    IntervalIntegrable (fun y ↦ K ![x,y]*f y) volume 0 x := by
  apply hf.intervalIntegrable.continuousOn_mul
  rw [uIcc_of_le hx.1]
  exact hK.comp (by fun_prop) (fun y hy ↦ ⟨hx,hy⟩)

/-- A continuous triangle kernel preserves integrability on an individual row. -/
theorem intervalIntegrable_continuousVolterra_mul_row
    {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
    {f : ℝ → ℝ} (x : Icc (0 : ℝ) 1)
    (hf : IntervalIntegrable f volume 0 (x : ℝ)) :
    IntervalIntegrable (fun y ↦ K ![(x : ℝ),y]*f y) volume 0 (x : ℝ) := by
  apply hf.continuousOn_mul
  rw [uIcc_of_le x.property.1]
  exact hK.comp (by fun_prop) (fun y hy ↦ ⟨x.property, hy⟩)

/-- Rowwise integrable inputs supply classical continuous-kernel Volterra data. -/
def VolterraIntegralInput.ofContinuousKernel
    {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
    {f : ℝ → ℝ} (x : Icc (0 : ℝ) 1)
    (hf : IntervalIntegrable f volume 0 (x : ℝ)) : VolterraIntegralInput (x : ℝ) :=
  .ofKernel K f (intervalIntegrable_continuousVolterra_mul_row hK x hf)

/-- Uniform kernel error bounds the output error for a fixed L¹ input. -/
theorem norm_volterraIntegral_sub_le_of_integrable
    {K L : (Fin 2 → ℝ) → ℝ}
    (hK : ContinuousOn K volterraTriangle) (hL : ContinuousOn L volterraTriangle)
    {f : ℝ → ℝ} (hf : Integrable f volume) {e : ℝ} (he : 0 ≤ e)
    (hb : ∀ z ∈ volterraTriangle, |K z-L z| ≤ e)
    (x : Icc (0 : ℝ) 1) :
    ‖volterraIntegral (.ofContinuousKernel hK x hf.intervalIntegrable) -
      volterraIntegral (.ofContinuousKernel hL x hf.intervalIntegrable)‖ ≤ e*∫ y in (0 : ℝ)..1, ‖f y‖ := by
  have hx := x.property
  simp only [VolterraIntegralInput.ofContinuousKernel, volterraIntegral_ofKernel]
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_continuousVolterra_mul hK hf hx)
    (intervalIntegrable_continuousVolterra_mul hL hf hx)]
  have hbound : ∀ᵐ y ∂volume, y ∈ Ioc (0 : ℝ) (x : ℝ) →
      ‖K ![x,y]*f y-L ![x,y]*f y‖ ≤ e*‖f y‖ := by
    apply Eventually.of_forall
    intro y hy
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb _ ⟨hx,hy.1.le,hy.2⟩) (norm_nonneg _)
  calc
    _ ≤ ∫ y in (0 : ℝ)..x, e*‖f y‖ :=
      intervalIntegral.norm_integral_le_of_norm_le hx.1 hbound
        (hf.norm.const_mul e).intervalIntegrable
    _ = e*∫ y in (0 : ℝ)..x, ‖f y‖ := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
        (Eventually.of_forall (fun y ↦ norm_nonneg (f y))) hf.norm.intervalIntegrable) he

/-- Uniform kernel convergence gives uniform primitive convergence for every integrable input. -/
theorem tendstoUniformly_volterraIntegral_of_integrable
    {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
    (p : ℕ → MvPolynomial (Fin 2) ℝ)
    {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n)
    (herr : ∀ n z, z ∈ volterraTriangle → |MvPolynomial.eval z (p n)-K z| ≤ e n)
    (hte : Tendsto e atTop (𝓝 0)) {f : ℝ → ℝ} (hf : Integrable f volume) :
    TendstoUniformly
      (fun n (x : Icc (0 : ℝ) 1) ↦ volterraIntegral
        (.ofPolynomial (p n) hf.locallyIntegrable (x : ℝ)))
      (fun x ↦ volterraIntegral (.ofContinuousKernel hK x hf.intervalIntegrable)) atTop := by
  have ht : Tendsto (fun n ↦ e n*∫ y in (0 : ℝ)..1, ‖f y‖) atTop (𝓝 0) := by
    simpa using hte.mul_const (∫ y in (0 : ℝ)..1, ‖f y‖)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x
  rw [dist_eq_norm, norm_sub_rev]
  simpa only [VolterraIntegralInput.ofPolynomial,
    VolterraIntegralInput.ofContinuousKernel, volterraIntegral_ofKernel] using
    (norm_volterraIntegral_sub_le_of_integrable (p n).continuous_eval.continuousOn
      hK hf (he n) (herr n) x).trans_lt hn

/-- Continuous triangle kernels send integrable inputs to continuous physical primitives. -/
theorem continuous_volterraIntegral_of_integrable
    {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
    {f : ℝ → ℝ} (hf : Integrable f volume) :
    Continuous (fun x : Icc (0 : ℝ) 1 ↦
      volterraIntegral (.ofContinuousKernel hK x hf.intervalIntegrable)) := by
  choose p hp using (fun n : ℕ ↦ MvPolynomial.exists_polynomial_near_volterraKernel hK
    (show 0 < (1/2 : ℝ)^n by positivity))
  have ht := tendstoUniformly_volterraIntegral_of_integrable hK p
    (fun n ↦ pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n)
    (fun n z hz ↦ (hp n z hz).le)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)) hf
  exact ht.continuous (Eventually.of_forall (fun n ↦
    (MvPolynomial.continuous_polynomialVolterraIntegral (p n) f hf.locallyIntegrable).comp
      continuous_subtype_val)).frequently

end Real
