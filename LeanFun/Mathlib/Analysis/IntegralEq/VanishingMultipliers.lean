/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.BoundedKernel
public import LeanFun.Mathlib.Analysis.IntegralEq.WeakKernel
public import LeanFun.Mathlib.Analysis.IntegralEq.L2Dominated
public import LeanFun.Mathlib.Analysis.Normed.Operator.FiniteSection

/-! # Vanishing output multipliers and compact kernels

Bounded multipliers tending pointwise to zero tend strongly to zero on L².
After composition with a compact map the convergence is in operator norm.
Reference: dominated convergence and uniform convergence on compact sets.
-/

public noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace MeasureTheory
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Move a real bounded multiplier across the L² pairing. -/
theorem inner_boundedMulL2 (q : X → ℝ) (hq : AEStronglyMeasurable q μ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ x ∂μ, ‖q x‖ ≤ M) (f g : Lp ℝ 2 μ) :
    ⟪g, boundedMulL2 μ q hq hM hb f⟫_ℝ = ⟪boundedMulL2 μ q hq hM hb g, f⟫_ℝ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMulL2_ae μ q hq hM hb f,
    boundedMulL2_ae μ q hq hM hb g] with x hf hg
  simp only [Real.inner_apply, hf, hg]
  ring

/-- Uniformly bounded multipliers vanishing almost everywhere converge strongly to zero. -/
theorem tendsto_boundedMulL2_zero (q : ℕ → X → ℝ)
    (hq : ∀ n, AEStronglyMeasurable (q n) μ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ n, ∀ᵐ x ∂μ, ‖q n x‖ ≤ M)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n ↦ q n x) atTop (𝓝 0)) (f : Lp ℝ 2 μ) :
    Tendsto (fun n ↦ boundedMulL2 μ (q n) (hq n) hM (hb n) f) atTop (𝓝 0) := by
  have h := tendsto_L2_of_dominated (fun n x ↦ q n x * f x) (fun _ ↦ 0)
    (fun n ↦ memLp_bounded_mul μ (q n) (hq n) (hb n) f) (MemLp.zero)
    (fun x ↦ M * |f x|)
    (by simpa only [mul_pow, sq_abs] using ((Lp.memLp f).integrable_sq.const_mul (M^2)))
    (fun n ↦ (hb n).mono (fun x hx ↦ by
      simpa only [sub_zero, abs_mul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right hx (abs_nonneg (f x))))
    (ht.mono (fun x hx ↦ by simpa using hx.mul_const (f x)))
  simpa [boundedMulL2, ← Pi.zero_def] using h

/-- A bounded output multiplier vanishing almost everywhere kills compact maps in norm. -/
theorem tendsto_boundedMulL2_comp_compact_zero (q : ℕ → X → ℝ)
    (hq : ∀ n, AEStronglyMeasurable (q n) μ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ n, ∀ᵐ x ∂μ, ‖q n x‖ ≤ M)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n ↦ q n x) atTop (𝓝 0))
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hT : IsCompactOperator T) :
    Tendsto (fun n ↦ (boundedMulL2 μ (q n) (hq n) hM (hb n)).comp T) atTop (𝓝 0) := by
  let Q n := boundedMulL2 μ (q n) (hq n) hM (hb n)
  have h := ContinuousLinearMap.tendsto_compact_comp_of_strongly_tendsto_id
    (fun n ↦ 1-Q n) (C := 1+M)
    (fun n ↦ (norm_sub_le _ _).trans (add_le_add (ContinuousLinearMap.norm_id_le)
      (norm_boundedMulL2_le μ (q n) (hq n) hM (hb n))))
    (fun f ↦ by simpa using tendsto_const_nhds.sub (tendsto_boundedMulL2_zero μ q hq hM hb ht f)) T hT
  have he (n : ℕ) : T-(1-Q n).comp T = (Q n).comp T := by
    ext f
    simp
  simpa only [he, sub_self] using (tendsto_const_nhds (x := T)).sub h


/-- A bounded output multiplier preserves integrable weak pairings and multiplies
the first kernel variable. Reference: bounded multipliers on real L². -/
theorem inner_boundedMulL2_comp_kernel [IsFiniteMeasure μ] (K : L2WeakKernel μ)
    (q : X → ℝ) (hq : AEStronglyMeasurable q μ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ x ∂μ, ‖q x‖ ≤ M)
    (f g : Lp ℝ 2 μ) :
    Integrable (fun z : X × X => (q z.1*K.kernel z)*(g z.1*f z.2)) (μ.prod μ) ∧
    ⟪g, (boundedMulL2 μ q hq hM hb).comp K.operator f⟫_ℝ =
      ∫ z, (q z.1*K.kernel z)*(g z.1*f z.2) ∂μ.prod μ := by
  constructor
  · apply (K.pair_integrable f (boundedMulL2 μ q hq hM hb g)).congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (boundedMulL2_ae μ q hq hM hb g)] with z hz
    rw [hz]
    ring
  · rw [ContinuousLinearMap.comp_apply,inner_boundedMulL2,K.pairing]
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (boundedMulL2_ae μ q hq hM hb g)] with z hz
    rw [hz]
    ring

end MeasureTheory
