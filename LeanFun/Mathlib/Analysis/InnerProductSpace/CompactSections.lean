/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.HilbertBasisOperator
public import LeanFun.Mathlib.Analysis.Normed.Operator.FiniteSection
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Operator-norm convergence of compact coefficient sections

Initial orthogonal projections converge uniformly after composition with a
compact operator, on either side. Reference: the compact finite-section
argument of Olver–Townsend (2013), Lemma 4.4.
-/

public noncomputable section
open Filter ContinuousLinearMap
open scoped Topology InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
namespace lp

/-- Initial coordinate projections have finite rank and are compact. -/
theorem isCompactOperator_initialL2Projection (N : ℕ) :
    IsCompactOperator (initialL2Projection (𝕜 := 𝕜) N) := by
  unfold initialL2Projection
  have h (s : Finset ℕ) : IsCompactOperator
      (∑ i ∈ s, (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i).comp
        (evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i) :
        lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero :
        IsCompactOperator (0 : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2))
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((isCompactOperator_of_locallyCompactSpace_rng
        (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i)).comp_clm _).add ih
  exact h _

/-- Coordinate truncations are self-adjoint. -/
theorem adjoint_initialL2Projection (N : ℕ) :
    (initialL2Projection (𝕜 := 𝕜) N).adjoint = initialL2Projection N := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left 𝕜
  intro x
  rw [adjoint_inner_right]
  simp only [initialL2Projection_apply, inner_sum, sum_inner,
    inner_single_left, inner_single_right]

/-- Applying an initial projection twice has the same effect as applying it once. -/
theorem initialL2Projection_idempotent (N : ℕ) :
    (initialL2Projection (𝕜 := 𝕜) N).comp (initialL2Projection N) = initialL2Projection N := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, initialL2Projection_apply, lp.coeFn_sum,
    lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single]
  split_ifs <;> simp_all

/-- Compact operators have operator-norm convergent output sections. -/
theorem tendsto_initialL2Projection_comp
    (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    (hT : IsCompactOperator T) :
    Tendsto (fun N ↦ (initialL2Projection N).comp T) atTop (𝓝 T) :=
  tendsto_compact_comp_of_strongly_tendsto_id _ norm_initialL2Projection_le
    tendsto_initialL2Projection T hT

/-- Compactness is preserved by the adjoint on sequence Hilbert space. -/
theorem isCompactOperator_adjoint_of_initialL2
    (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    (hT : IsCompactOperator T) : IsCompactOperator T.adjoint := by
  have ht := (ContinuousLinearMap.adjoint.continuous.tendsto _).comp
    (tendsto_initialL2Projection_comp T hT)
  apply isCompactOperator_of_tendsto ht
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_apply]
  rw [adjoint_comp, adjoint_initialL2Projection]
  exact (isCompactOperator_initialL2Projection N).clm_comp T.adjoint

/-- Compact operators have operator-norm convergent input sections. -/
theorem tendsto_comp_initialL2Projection
    (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    (hT : IsCompactOperator T) :
    Tendsto (fun N ↦ T.comp (initialL2Projection N)) atTop (𝓝 T) := by
  have ht := (ContinuousLinearMap.adjoint.continuous.tendsto _).comp
    (tendsto_initialL2Projection_comp T.adjoint
      (isCompactOperator_adjoint_of_initialL2 T hT))
  simpa only [Function.comp_def, adjoint_comp, adjoint_adjoint, adjoint_initialL2Projection] using ht

/-- Leading input and output sections converge in operator norm for compact operators. -/
theorem tendsto_initialL2Sections_norm
    (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    (hT : IsCompactOperator T) :
    Tendsto (fun N ↦ (initialL2Projection N).comp (T.comp (initialL2Projection N)))
      atTop (𝓝 T) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ho := (tendsto_initialL2Projection_comp T hT).sub (tendsto_const_nhds (x := T))
  have hi := (tendsto_comp_initialL2Projection T hT).sub (tendsto_const_nhds (x := T))
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun N ↦ show ‖(initialL2Projection N).comp (T.comp (initialL2Projection N)) - T‖ ≤
      ‖T.comp (initialL2Projection N) - T‖ + ‖(initialL2Projection N).comp T - T‖ from ?_)
    (by simpa using hi.norm.add ho.norm)
  calc
    _ ≤ ‖(initialL2Projection N).comp (T.comp (initialL2Projection N)) -
          (initialL2Projection N).comp T‖ + ‖(initialL2Projection N).comp T - T‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      rw [← comp_sub]
      exact (opNorm_comp_le _ _).trans
        (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
          (norm_initialL2Projection_le (𝕜 := 𝕜) N) (norm_nonneg _)))

end lp
