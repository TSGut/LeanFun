/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.Schur
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Bounded signed kernels on finite measure spaces

A bounded multiplier on the product L² space, between the two coordinate
pullbacks, defines the integral operator. Reference: the bounded-kernel
special case of the Schur test. Kernels may have either sign.
-/

@[expose] public noncomputable section
open scoped ENNReal InnerProductSpace
namespace MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A bounded measurable multiplier preserves L². -/
theorem memLp_bounded_mul (μ : Measure X) (k : X → 𝕜) (hk : AEStronglyMeasurable k μ)
    {M : ℝ} (hb : ∀ᵐ x ∂μ, ‖k x‖ ≤ M) (u : Lp 𝕜 2 μ) :
    MemLp (fun x ↦ k x * u x) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := M) (hk.mul (Lp.aestronglyMeasurable u))
  filter_upwards [hb] with x hx
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- Multiplication by an essentially bounded scalar function on L². -/
def boundedMulL2 (μ : Measure X) (k : X → 𝕜) (hk : AEStronglyMeasurable k μ)
    {M : ℝ} (_hM : 0 ≤ M) (hb : ∀ᵐ x ∂μ, ‖k x‖ ≤ M) : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuous
    { toFun u := (memLp_bounded_mul μ k hk hb u).toLp _
      map_add' u v := by
        apply Lp.ext
        filter_upwards [(memLp_bounded_mul μ k hk hb (u+v)).coeFn_toLp,
          (memLp_bounded_mul μ k hk hb u).coeFn_toLp,
          (memLp_bounded_mul μ k hk hb v).coeFn_toLp, Lp.coeFn_add u v,
          Lp.coeFn_add ((memLp_bounded_mul μ k hk hb u).toLp _)
            ((memLp_bounded_mul μ k hk hb v).toLp _)] with x ha hu hv huv hs
        simp only [ha, hs, hu, hv, huv, Pi.add_apply, mul_add]
      map_smul' r u := by
        change (memLp_bounded_mul μ k hk hb (r • u)).toLp _ = r • _
        apply Lp.ext
        filter_upwards [(memLp_bounded_mul μ k hk hb (r • u)).coeFn_toLp,
          (memLp_bounded_mul μ k hk hb u).coeFn_toLp, Lp.coeFn_smul r u,
          Lp.coeFn_smul r ((memLp_bounded_mul μ k hk hb u).toLp _)] with x ha hu hru hs
        simp only [ha, hs, hu, hru, Pi.smul_apply, smul_eq_mul]
        ring }
    M (fun u ↦ Lp.norm_le_mul_norm_of_ae_le_mul (by
      change ∀ᵐ x ∂μ, ‖(memLp_bounded_mul μ k hk hb u).toLp _ x‖ ≤ M * ‖u x‖
      filter_upwards [(memLp_bounded_mul μ k hk hb u).coeFn_toLp, hb] with x hx hkx
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right hkx (norm_nonneg _)))

/-- The multiplier has its expected almost-everywhere representative. -/
theorem boundedMulL2_ae (μ : Measure X) (k : X → 𝕜) (hk : AEStronglyMeasurable k μ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ x ∂μ, ‖k x‖ ≤ M) (u : Lp 𝕜 2 μ) :
    boundedMulL2 μ k hk hM hb u =ᵐ[μ] fun x ↦ k x * u x :=
  (memLp_bounded_mul μ k hk hb u).coeFn_toLp

/-- The essential multiplier bound controls the operator norm. -/
theorem norm_boundedMulL2_le (μ : Measure X) (k : X → 𝕜) (hk : AEStronglyMeasurable k μ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ x ∂μ, ‖k x‖ ≤ M) :
    ‖boundedMulL2 μ k hk hM hb‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMulL2_ae μ k hk hM hb u, hb] with x hx hkx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hkx (norm_nonneg _)

variable (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (k : X × Y → ℝ) (hk : AEStronglyMeasurable k (μ.prod ν))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ z ∂μ.prod ν, ‖k z‖ ≤ M)

/-- Integral operator of a bounded signed kernel between finite measure spaces. -/
def boundedKernelL2Operator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (dominatedL2Pullback μ (μ.prod ν) Prod.fst measurable_fst (measure_ne_top ν Set.univ) (by simp)).adjoint.comp
    ((boundedMulL2 (μ.prod ν) k hk hM hb).comp
      (dominatedL2Pullback ν (μ.prod ν) Prod.snd measurable_snd (measure_ne_top μ Set.univ) (by simp)))

/-- Finite measure masses and the kernel bound control the operator norm. -/
theorem norm_boundedKernelL2Operator_le :
    ‖boundedKernelL2Operator μ ν k hk hM hb‖ ≤
      Real.sqrt (ν Set.univ).toReal * (M * Real.sqrt (μ Set.univ).toReal) := by
  unfold boundedKernelL2Operator
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [ContinuousLinearMap.adjoint.norm_map]
  apply mul_le_mul (norm_dominatedL2Pullback_le _ _ _ _ _ _) _ (norm_nonneg _) (by positivity)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (norm_boundedMulL2_le _ _ _ _ _) (norm_dominatedL2Pullback_le _ _ _ _ _ _)
      (norm_nonneg _) hM)

/-- The bounded-kernel operator has the expected weak integral pairing. -/
theorem inner_boundedKernelL2Operator (f : Lp ℝ 2 ν) (g : Lp ℝ 2 μ) :
    ⟪g, boundedKernelL2Operator μ ν k hk hM hb f⟫_ℝ =
      ∫ z, k z * (g z.1 * f z.2) ∂μ.prod ν := by
  rw [boundedKernelL2Operator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMulL2_ae (μ.prod ν) k hk hM hb
      (dominatedL2Pullback ν (μ.prod ν) Prod.snd measurable_snd (measure_ne_top μ Set.univ) (by simp) f),
    dominatedL2Pullback_ae μ (μ.prod ν) Prod.fst measurable_fst (measure_ne_top ν Set.univ) (by simp) g,
    dominatedL2Pullback_ae ν (μ.prod ν) Prod.snd measurable_snd (measure_ne_top μ Set.univ) (by simp) f]
    with z hz hg hf
  simp only [hz, hg, hf, Function.comp_apply, Real.inner_apply]
  ring

include hk hM hb in
/-- Every weak pairing for a bounded kernel is absolutely integrable. -/
theorem integrable_boundedKernelL2_pair (f : Lp ℝ 2 ν) (g : Lp ℝ 2 μ) :
    Integrable (fun z ↦ k z * (g z.1*f z.2)) (μ.prod ν) := by
  let hf := dominatedL2Pullback ν (μ.prod ν) Prod.snd measurable_snd (measure_ne_top μ Set.univ) (by simp) f
  let hg := dominatedL2Pullback μ (μ.prod ν) Prod.fst measurable_fst (measure_ne_top ν Set.univ) (by simp) g
  apply (L2.integrable_inner (𝕜 := ℝ) (boundedMulL2 (μ.prod ν) k hk hM hb hf) hg).congr
  filter_upwards [boundedMulL2_ae (μ.prod ν) k hk hM hb hf,
    dominatedL2Pullback_ae μ (μ.prod ν) Prod.fst measurable_fst (measure_ne_top ν Set.univ) (by simp) g,
    dominatedL2Pullback_ae ν (μ.prod ν) Prod.snd measurable_snd (measure_ne_top μ Set.univ) (by simp) f]
    with z hz hgz hfz
  dsimp only [hf, hg] at hz ⊢
  simp only [Real.inner_apply, hz, hgz, hfz, Function.comp_apply]
  ring

end MeasureTheory
