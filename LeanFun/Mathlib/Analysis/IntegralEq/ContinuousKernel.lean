/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.BoundedKernel
public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousRows
public import LeanFun.Mathlib.Analysis.IntegralEq.L2Dominated

/-! # Compact continuous bounded kernels on compactly supported measures

Continuous bounded kernels have continuous L² rows. Finite coordinate
approximation of these rows proves compactness. Reference: the classical
finite-rank approximation argument for continuous integral kernels.
-/

@[expose] public noncomputable section
open Set Filter ContinuousLinearMap
open scoped ENNReal Topology InnerProductSpace
namespace MeasureTheory
variable (μ : Measure ℝ) [IsFiniteMeasure μ]
  {k : ℝ × ℝ → ℝ} (hk : Continuous k) {M : ℝ} (hM : 0 ≤ M)
  (hb : ∀ z, ‖k z‖ ≤ M)

include hk hb in
/-- A bounded continuous kernel row belongs to L². -/
theorem memLp_continuousKernel_row (x : ℝ) : MemLp (fun y ↦ k (x,y)) 2 μ :=
  MemLp.of_bound (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable M
    (Eventually.of_forall (fun y ↦ hb (x,y)))

/-- The L² vector represented by a continuous bounded kernel row. -/
def continuousKernelRow (x : ℝ) : Lp ℝ 2 μ :=
  (memLp_continuousKernel_row μ hk hb x).toLp _

/-- Kernel rows have their prescribed representatives. -/
theorem continuousKernelRow_ae (x : ℝ) :
    continuousKernelRow μ hk hb x =ᵐ[μ] fun y ↦ k (x,y) :=
  (memLp_continuousKernel_row μ hk hb x).coeFn_toLp

/-- Pairing a row with an L² vector is the kernel integral. -/
theorem inner_continuousKernelRow (x : ℝ) (f : Lp ℝ 2 μ) :
    ⟪continuousKernelRow μ hk hb x, f⟫_ℝ = ∫ y, k (x,y)*f y ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousKernelRow_ae μ hk hb x] with y hy
  simp only [Real.inner_apply, hy]

include hM in
/-- Uniform bounds on the kernel give uniform bounds on row norms. -/
theorem norm_continuousKernelRow_le (x : ℝ) :
    ‖continuousKernelRow μ hk hb x‖ ≤ (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * M := by
  apply Lp.norm_le_of_ae_bound hM
  filter_upwards [continuousKernelRow_ae μ hk hb x] with y hy
  rw [hy]
  exact hb (x,y)

include hM in
/-- The row pairing is an L² function of the output coordinate. -/
theorem memLp_inner_continuousKernelRow (f : Lp ℝ 2 μ) :
    MemLp (fun x ↦ ⟪continuousKernelRow μ hk hb x, f⟫_ℝ) 2 μ := by
  have hf := (Lp.memLp f).aestronglyMeasurable.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have hm := (hk.aestronglyMeasurable.mul hf).integral_prod_right'
  simp only [Function.comp_def, Pi.mul_apply] at hm
  simp_rw [← inner_continuousKernelRow μ hk hb] at hm
  apply MemLp.of_bound hm
    (((measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * M) * ‖f‖)
  exact Eventually.of_forall (fun x ↦ (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_continuousKernelRow_le μ hk hM hb x) (norm_nonneg _)))

/-- The bounded-kernel operator is represented by the row inner products. -/
theorem boundedKernelL2Operator_ae_inner_row (f : Lp ℝ 2 μ) :
    boundedKernelL2Operator μ μ k hk.aestronglyMeasurable hM (Eventually.of_forall hb) f =ᵐ[μ]
      fun x ↦ ⟪continuousKernelRow μ hk hb x, f⟫_ℝ := by
  let hg := memLp_inner_continuousKernelRow μ hk hM hb f
  have he : boundedKernelL2Operator μ μ k hk.aestronglyMeasurable hM
      (Eventually.of_forall hb) f = hg.toLp _ := by
    apply ext_inner_left ℝ
    intro g
    rw [inner_boundedKernelL2Operator, integral_prod _
      (integrable_boundedKernelL2_pair μ μ k hk.aestronglyMeasurable hM
        (Eventually.of_forall hb) f g), L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [Real.inner_apply, hx, inner_continuousKernelRow]
    simp_rw [show ∀ y, k (x,y)*(g x*f y) = g x*(k (x,y)*f y) by intro y; ring]
    rw [integral_const_mul]
  rw [he]
  exact hg.coeFn_toLp

/-- Bounded continuous kernels have continuous L² rows. -/
theorem continuous_continuousKernelRow : Continuous (continuousKernelRow μ hk hb) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_L2_of_dominated (fun s y ↦ k (s,y)) (fun y ↦ k (x,y))
    (fun s ↦ memLp_continuousKernel_row μ hk hb s) (memLp_continuousKernel_row μ hk hb x)
    (fun _ ↦ 2*M) (integrable_const _)
  · intro s
    exact Eventually.of_forall (fun y ↦ (abs_sub _ _).trans
      ((add_le_add (hb (s,y)) (hb (x,y))).trans_eq (by ring)))
  · exact Eventually.of_forall (fun y ↦ (hk.comp (continuous_id.prodMk continuous_const)).continuousAt)

/-- A continuous bounded kernel is compact when the finite measure has compact support. -/
theorem isCompactOperator_boundedKernelL2Operator_of_continuous
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) {S : Set ℝ} (hS : IsCompact S)
    (hs : ∀ᵐ x ∂μ, x ∈ S) :
    IsCompactOperator (boundedKernelL2Operator μ μ k hk.aestronglyMeasurable hM
      (Eventually.of_forall hb)) := by
  let T := boundedKernelL2Operator μ μ k hk.aestronglyMeasurable hM (Eventually.of_forall hb)
  let U := T.comp b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hc : IsCompactOperator U := by
    apply isCompactOperator_of_continuous_L2_rows μ U
      (fun x ↦ b.repr (continuousKernelRow μ hk hb x)) hS
    · exact (b.repr.continuous.comp (continuous_continuousKernelRow μ hk hb)).continuousOn
    · exact hs
    · intro f
      filter_upwards [boundedKernelL2Operator_ae_inner_row μ hk hM hb (b.repr.symm f)] with x hx
      change T (b.repr.symm f) x = _
      rw [hx, ← b.repr.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  have he : U.comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap = T := by
    apply ContinuousLinearMap.ext
    intro f
    change T (b.repr.symm (b.repr f)) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [show boundedKernelL2Operator μ μ k hk.aestronglyMeasurable hM
    (Eventually.of_forall hb) = T from rfl, ← he]
  exact hc.comp_clm _

end MeasureTheory
