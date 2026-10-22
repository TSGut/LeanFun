/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Synthesis of orthogonal contractions on a Hilbert sum
A family of contractions with mutually orthogonal images sums to a contraction
from their ℓ² sum. We use Mathlib's orthogonal-family synthesis on the ranges;
the individual maps need not be isometries or have closed ranges.
-/

@[expose] public noncomputable section
namespace lp

variable {ι : Type*} {G : ι → Type*} {E : Type*}
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℝ (G i)]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (T : ∀ i, G i →L[ℝ] E)
  (hT : ∀ i x, ‖T i x‖ ≤ ‖x‖)
  (horth : ∀ i j, i ≠ j → ∀ x y, inner ℝ (T i x) (T j y) = 0)

omit [CompleteSpace E] in
include horth in
/-- The images of mutually orthogonal operators form an orthogonal family of subspaces. -/
theorem orthogonalFamily_range :
    OrthogonalFamily ℝ (fun i ↦ LinearMap.range (T i).toLinearMap)
      (fun i ↦ (LinearMap.range (T i).toLinearMap).subtypeₗᵢ) := by
  intro i j hij x y
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  change inner ℝ (x : E) (y : E) = 0
  rw [← ha, ← hb]
  exact horth i j hij a b

/-- Apply the contractions coordinatewise, retaining their range subspaces. -/
def rangeCoordinates : lp G 2 →L[ℝ] lp (fun i ↦ LinearMap.range (T i).toLinearMap) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟨fun i ↦ ⟨T i (x i), LinearMap.mem_range_self _ _⟩,
        (lp.memℓp x).mono' (fun i ↦ hT i (x i))⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        apply Subtype.ext
        exact map_add (T i) _ _
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        apply Subtype.ext
        exact map_smul (T i) c _ }
    1 (by
      intro x
      simpa only [one_mul] using
        (lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun i ↦ hT i (x i))))

/-- Orthogonal contractions synthesize to a continuous map from the full Hilbert sum. -/
def orthogonalSynthesis : lp G 2 →L[ℝ] E :=
  (orthogonalFamily_range T horth).linearIsometry.toContinuousLinearMap.comp (rangeCoordinates T hT)

/-- Synthesis is the unconditionally convergent sum of the coordinate images. -/
theorem hasSum_orthogonalSynthesis (x : lp G 2) :
    HasSum (fun i ↦ T i (x i)) (orthogonalSynthesis T hT horth x) :=
  (orthogonalFamily_range T horth).hasSum_linearIsometry (rangeCoordinates T hT x)

/-- The synthesis map has the expected infinite-series formula. -/
theorem orthogonalSynthesis_apply (x : lp G 2) :
    orthogonalSynthesis T hT horth x = ∑' i, T i (x i) :=
  (hasSum_orthogonalSynthesis T hT horth x).tsum_eq.symm

/-- Orthogonal synthesis does not increase the Hilbert-sum norm. -/
theorem norm_orthogonalSynthesis_le (x : lp G 2) :
    ‖orthogonalSynthesis T hT horth x‖ ≤ ‖x‖ := by
  change ‖(orthogonalFamily_range T horth).linearIsometry (rangeCoordinates T hT x)‖ ≤ _
  rw [LinearIsometry.norm_map]
  exact lp.norm_mono (by norm_num) (fun i ↦ hT i (x i))

/-- A single nonzero coordinate synthesizes to precisely its operator image. -/
theorem orthogonalSynthesis_single [DecidableEq ι] (i : ι) (x : G i) :
    orthogonalSynthesis T hT horth (lp.single 2 i x) = T i x := by
  rw [orthogonalSynthesis_apply, tsum_eq_single i]
  · simp [lp.single_apply]
  · intro j hj
    simp [lp.single_apply, hj]

/-- Synthesis is faithful when each coordinate operator is faithful. -/
theorem orthogonalSynthesis_injective (hi : ∀ i, Function.Injective (T i)) :
    Function.Injective (orthogonalSynthesis T hT horth) := by
  intro x y h
  have he := (orthogonalFamily_range T horth).linearIsometry.injective h
  apply lp.ext
  funext i
  apply hi i
  exact congrArg (fun z : lp (fun i ↦ LinearMap.range (T i).toLinearMap) 2 ↦ (z i : E)) he

end lp
