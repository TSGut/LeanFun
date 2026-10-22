/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.BoundedKernel
/-! # Bounded kernels on a joint measure with prescribed marginals

Pullback along the two coordinates and the adjoint of the first pullback
realize a bounded signed kernel between the two marginal L² spaces.
This is the exact-marginal form of the Schur construction.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) (κ : Measure (X × Y))
    (hfst : κ.map Prod.fst = μ) (hsnd : κ.map Prod.snd = ν)
    (k : X × Y → ℝ) (hk : AEStronglyMeasurable k κ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ z ∂κ, ‖k z‖ ≤ M)
/-- The bounded operator represented weakly by a joint-measure kernel. -/
def marginalKernelL2Operator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (dominatedL2Pullback μ κ Prod.fst measurable_fst ENNReal.one_ne_top
    (by rw [one_smul, hfst])).adjoint.comp
      ((boundedMulL2 κ k hk hM hb).comp
        (dominatedL2Pullback ν κ Prod.snd measurable_snd ENNReal.one_ne_top
          (by rw [one_smul, hsnd])))
/-- The weak integral formula defining the marginal kernel operator. -/
theorem inner_marginalKernelL2Operator (f : Lp ℝ 2 ν) (g : Lp ℝ 2 μ) :
    ⟪g, marginalKernelL2Operator μ ν κ hfst hsnd k hk hM hb f⟫_ℝ =
      ∫ z, k z * (g z.1*f z.2) ∂κ := by
  rw [marginalKernelL2Operator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMulL2_ae κ k hk hM hb
      (dominatedL2Pullback ν κ Prod.snd measurable_snd ENNReal.one_ne_top
        (by rw [one_smul, hsnd]) f),
    dominatedL2Pullback_ae μ κ Prod.fst measurable_fst ENNReal.one_ne_top
      (by rw [one_smul, hfst]) g,
    dominatedL2Pullback_ae ν κ Prod.snd measurable_snd ENNReal.one_ne_top
      (by rw [one_smul, hsnd]) f] with z hz hg hf
  simp only [hz, hg, hf, Function.comp_apply, Real.inner_apply]
  ring
/-- The operator norm is bounded by the essential bound of the kernel. -/
theorem norm_marginalKernelL2Operator_le :
    ‖marginalKernelL2Operator μ ν κ hfst hsnd k hk hM hb‖ ≤ M := by
  have hx := norm_dominatedL2Pullback_le μ κ Prod.fst measurable_fst
    ENNReal.one_ne_top (by rw [one_smul, hfst])
  have hy := norm_dominatedL2Pullback_le ν κ Prod.snd measurable_snd
    ENNReal.one_ne_top (by rw [one_smul, hsnd])
  norm_num only [ENNReal.toReal_one, Real.sqrt_one] at hx hy
  have hm := norm_boundedMulL2_le κ k hk hM hb
  unfold marginalKernelL2Operator
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [ContinuousLinearMap.adjoint.norm_map]
  calc
    _ ≤ 1 * (M * 1) := mul_le_mul hx
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hm hy (norm_nonneg _) hM)) (norm_nonneg _) (by norm_num)
    _ = M := by ring
include hfst hsnd hk hM hb in
/-- The weak kernel pairing is absolutely integrable for any two L² inputs. -/
theorem integrable_marginalKernelL2_pair (f : Lp ℝ 2 ν) (g : Lp ℝ 2 μ) :
    Integrable (fun z ↦ k z * (g z.1*f z.2)) κ := by
  let f' := dominatedL2Pullback ν κ Prod.snd measurable_snd ENNReal.one_ne_top
    (by rw [one_smul, hsnd]) f
  let g' := dominatedL2Pullback μ κ Prod.fst measurable_fst ENNReal.one_ne_top
    (by rw [one_smul, hfst]) g
  apply (L2.integrable_inner (𝕜 := ℝ) (boundedMulL2 κ k hk hM hb f') g').congr
  filter_upwards [boundedMulL2_ae κ k hk hM hb f',
    dominatedL2Pullback_ae μ κ Prod.fst measurable_fst ENNReal.one_ne_top
      (by rw [one_smul, hfst]) g,
    dominatedL2Pullback_ae ν κ Prod.snd measurable_snd ENNReal.one_ne_top
      (by rw [one_smul, hsnd]) f] with z hz hgz hfz
  dsimp only [f', g'] at hz ⊢
  simp only [Real.inner_apply, hz, hgz, hfz, Function.comp_apply]
  ring
end MeasureTheory
