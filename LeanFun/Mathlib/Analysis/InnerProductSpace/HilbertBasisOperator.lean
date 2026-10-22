/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.NormNum

/-! # Hilbert coordinates and strong convergence of finite sections

Unitary coordinate transport preserves the norm of a bounded operator.
Leading finite input and output sections converge strongly on every ℓ² vector.
Reference: the Hilbert-space orthonormal expansion theorem, DLMF 18.2(viii).
-/

@[expose] public noncomputable section
open Filter
open scoped ENNReal Topology InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
namespace lp

/-- Projection onto the first `N` coordinates in ℓ². -/
def initialL2Projection (N : ℕ) :
    lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 :=
  ∑ i ∈ Finset.range N,
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i).comp
      (lp.evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i)

/-- The initial projection is the finite sum of coordinate vectors. -/
theorem initialL2Projection_apply (N : ℕ) (c : lp (fun _ : ℕ ↦ 𝕜) 2) :
    initialL2Projection N c = ∑ i ∈ Finset.range N, lp.single 2 i (c i) := by
  simp only [initialL2Projection, sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rfl

/-- Truncating an ℓ² vector cannot increase its norm. -/
theorem norm_initialL2Projection_apply_le (N : ℕ) (c : lp (fun _ : ℕ ↦ 𝕜) 2) :
    ‖initialL2Projection N c‖ ≤ ‖c‖ := by
  rw [initialL2Projection_apply]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single,
    Finset.mem_range]
  split_ifs <;> simp

/-- Initial coordinate projections are contractions. -/
theorem norm_initialL2Projection_le (N : ℕ) : ‖initialL2Projection (𝕜 := 𝕜) N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro c
  simpa only [one_mul] using norm_initialL2Projection_apply_le N c

/-- Initial coordinate projections converge strongly to the identity. -/
theorem tendsto_initialL2Projection (c : lp (fun _ : ℕ ↦ 𝕜) 2) :
    Tendsto (fun N ↦ initialL2Projection N c) atTop (𝓝 c) := by
  simpa only [initialL2Projection_apply] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) c).tendsto_sum_nat

/-- The finite-section error is controlled by the input and output tails. -/
theorem norm_initialL2Sections_sub_le
    (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    (c : lp (fun _ : ℕ ↦ 𝕜) 2) (N : ℕ) :
    ‖initialL2Projection N (T (initialL2Projection N c)) - T c‖ ≤
      ‖T‖*‖initialL2Projection N c-c‖+‖initialL2Projection N (T c)-T c‖ := by
  calc
    _ ≤ ‖initialL2Projection N (T (initialL2Projection N c)) - initialL2Projection N (T c)‖ +
        ‖initialL2Projection N (T c)-T c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖T‖*‖initialL2Projection N c-c‖ + ‖initialL2Projection N (T c)-T c‖ := by
      apply add_le_add _ le_rfl
      rw [← map_sub, ← map_sub]
      exact (norm_initialL2Projection_apply_le N _).trans (T.le_opNorm _)


/-- Leading input and output sections converge strongly for every bounded ℓ² operator. -/
theorem tendsto_initialL2Sections
    (T : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
    (c : lp (fun _ : ℕ ↦ 𝕜) 2) :
    Tendsto (fun N ↦ ∑ i ∈ Finset.range N, lp.single 2 i
      (T (∑ j ∈ Finset.range N, lp.single 2 j (c j)) i)) atTop (𝓝 (T c)) := by
  have hc := tendsto_initialL2Projection c
  have hTc := tendsto_initialL2Projection (T c)
  have hz : Tendsto (fun N ↦ initialL2Projection N (T (initialL2Projection N c)) - T c)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N ↦ ?_)
      (show Tendsto (fun N ↦ ‖T‖*‖initialL2Projection N c-c‖+
        ‖initialL2Projection N (T c)-T c‖) atTop (𝓝 0) from by
          simpa using ((hc.sub (tendsto_const_nhds (x := c))).norm.const_mul ‖T‖).add
            (hTc.sub (tendsto_const_nhds (x := T c))).norm)
    exact norm_initialL2Sections_sub_le T c N
  have hh := hz.add_const (T c)
  simpa only [sub_add_cancel, zero_add, initialL2Projection_apply] using hh

end lp

namespace HilbertBasis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A bounded operator expressed in orthonormal Hilbert coordinates. -/
def coefficientOperator (b : HilbertBasis ℕ 𝕜 E) (T : E →L[𝕜] E) :
    lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 :=
  b.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The transported operator agrees exactly with Hilbert-basis coordinates. -/
theorem coefficientOperator_repr (b : HilbertBasis ℕ 𝕜 E) (T : E →L[𝕜] E) (f : E) :
    b.coefficientOperator T (b.repr f) = b.repr (T f) := by
  change b.repr (T (b.repr.symm (b.repr f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- Orthonormal coordinate transport preserves the operator norm exactly. -/
theorem norm_coefficientOperator (b : HilbertBasis ℕ 𝕜 E) (T : E →L[𝕜] E) :
    ‖b.coefficientOperator T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro c
    change ‖b.repr (T (b.repr.symm c))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    simpa using T.le_opNorm (b.repr.symm c)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have hh := (b.coefficientOperator T).le_opNorm (b.repr f)
    simpa only [coefficientOperator_repr, LinearIsometryEquiv.norm_map] using hh

/-- Coordinate transport commutes with operator subtraction. -/
theorem coefficientOperator_sub (b : HilbertBasis ℕ 𝕜 E) (S T : E →L[𝕜] E) :
    b.coefficientOperator (S - T) = b.coefficientOperator S - b.coefficientOperator T := by
  apply ContinuousLinearMap.ext
  intro c
  simp only [coefficientOperator, ContinuousLinearMap.comp_apply, sub_apply, map_sub,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]

/-- Differences have exactly the same norm in normalized coefficient coordinates. -/
theorem norm_coefficientOperator_sub (b : HilbertBasis ℕ 𝕜 E) (S T : E →L[𝕜] E) :
    ‖b.coefficientOperator S - b.coefficientOperator T‖ = ‖S - T‖ := by
  rw [← coefficientOperator_sub, norm_coefficientOperator]

/-- A matrix entry is the inner product of a basis vector with the image of another. -/
theorem coefficientOperator_single (b : HilbertBasis ℕ 𝕜 E) (T : E →L[𝕜] E) (i j : ℕ) :
    b.coefficientOperator T (lp.single 2 j 1) i = ⟪b i, T (b j)⟫_𝕜 := by
  change b.repr (T (b.repr.symm (lp.single 2 j 1))) i = _
  rw [b.repr_symm_single, b.repr_apply_apply]

end HilbertBasis
