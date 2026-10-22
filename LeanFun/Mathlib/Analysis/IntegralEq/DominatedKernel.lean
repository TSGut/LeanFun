/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.Schur

/-! # Operator norms from domination of weak kernels

A signed kernel dominated by a positive bounded kernel inherits its norm
bound. Reference: the domination form of the Schur test.
-/

public noncomputable section
open scoped InnerProductSpace
namespace MeasureTheory
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

private theorem norm_norm_toLp (f : Lp ℝ 2 μ) :
    ‖(Lp.memLp f).norm.toLp (fun x ↦ ‖f x‖)‖ = ‖f‖ := by
  rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f), Lp.norm_def]

variable [SFinite μ]

/-- Domination of weak kernels controls operator norms. Both weak pairings are
assumed absolutely integrable, so no pointwise representative is required. -/
theorem norm_le_of_dominated_weak_kernel
    (T S : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (k q : X × X → ℝ)
    (ik : ∀ f g : Lp ℝ 2 μ, Integrable (fun z ↦ k z*(g z.1*f z.2)) (μ.prod μ))
    (iq : ∀ f g : Lp ℝ 2 μ, Integrable (fun z ↦ q z*(g z.1*f z.2)) (μ.prod μ))
    (hT : ∀ f g, ⟪g, T f⟫_ℝ = ∫ z, k z*(g z.1*f z.2) ∂μ.prod μ)
    (hS : ∀ f g, ⟪g, S f⟫_ℝ = ∫ z, q z*(g z.1*f z.2) ∂μ.prod μ)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ᵐ z ∂μ.prod μ, ‖k z‖ ≤ c*q z) :
    ‖T‖ ≤ c*‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (mul_nonneg hc (norm_nonneg S))
  intro f g hf hg
  let f0 := (Lp.memLp f).norm.toLp (fun x ↦ ‖f x‖)
  let g0 := (Lp.memLp g).norm.toLp (fun x ↦ ‖g x‖)
  have hef := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp
    (Lp.memLp f).norm.coeFn_toLp
  have heg := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp
    (Lp.memLp g).norm.coeFn_toLp
  have hbound : ‖⟪g, T f⟫_ℝ‖ ≤ c*⟪g0, S f0⟫_ℝ := by
    rw [hT, hS, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_ae (ik f g).norm
      ((iq f0 g0).const_mul c) ?_)
    filter_upwards [hb, hef, heg] with z hz hfz hgz
    change f0 z.2 = ‖f z.2‖ at hfz
    change g0 z.1 = ‖g z.1‖ at hgz
    rw [hfz, hgz, norm_mul, norm_mul]
    nlinarith [mul_le_mul_of_nonneg_right hz (mul_nonneg (norm_nonneg (g z.1))
      (norm_nonneg (f z.2)))]
  have hn : ⟪g0, S f0⟫_ℝ ≤ ‖S‖ := by
    apply (real_inner_le_norm _ _).trans
    calc
      ‖g0‖*‖S f0‖ ≤ ‖g0‖*(‖S‖*‖f0‖) :=
        mul_le_mul_of_nonneg_left (S.le_opNorm f0) (norm_nonneg _)
      _ = ‖S‖ := by rw [norm_norm_toLp, norm_norm_toLp, hf, hg]; ring
  change ⟪T f, g⟫_ℝ ≤ _
  rw [real_inner_comm]
  exact (le_abs_self _).trans (hbound.trans (mul_le_mul_of_nonneg_left hn hc))

end MeasureTheory
