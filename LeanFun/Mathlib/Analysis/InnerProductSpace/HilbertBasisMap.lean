/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.HilbertBasisOperator

/-! # Operators between two Hilbert bases

Source and target bases may belong to different Hilbert spaces. Orthonormal
coordinate transport preserves operator norms. Reference: Hilbert-space
orthonormal expansions (DLMF 18.2(viii)).
-/

@[expose] public noncomputable section
open scoped ENNReal InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
namespace HilbertBasis
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A bounded operator expressed in orthonormal Hilbert coordinates. -/
def coefficientMap (a : HilbertBasis ℕ 𝕜 E) (b : HilbertBasis ℕ 𝕜 F) (T : E →L[𝕜] F) :
    lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 :=
  b.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp a.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The transported operator agrees exactly with Hilbert-basis coordinates. -/
theorem coefficientMap_repr (a : HilbertBasis ℕ 𝕜 E) (b : HilbertBasis ℕ 𝕜 F) (T : E →L[𝕜] F) (f : E) :
    a.coefficientMap b T (a.repr f) = b.repr (T f) := by
  change b.repr (T (a.repr.symm (a.repr f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- Orthonormal coordinate transport preserves the operator norm exactly. -/
theorem norm_coefficientMap (a : HilbertBasis ℕ 𝕜 E) (b : HilbertBasis ℕ 𝕜 F) (T : E →L[𝕜] F) :
    ‖a.coefficientMap b T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro c
    change ‖b.repr (T (a.repr.symm c))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    simpa using T.le_opNorm (a.repr.symm c)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have hh := (a.coefficientMap b T).le_opNorm (a.repr f)
    simpa only [coefficientMap_repr, LinearIsometryEquiv.norm_map] using hh

/-- A matrix entry is the inner product of a basis vector with the image of another. -/
theorem coefficientMap_single (a : HilbertBasis ℕ 𝕜 E) (b : HilbertBasis ℕ 𝕜 F) (T : E →L[𝕜] F) (i j : ℕ) :
    a.coefficientMap b T (lp.single 2 j 1) i = ⟪b i, T (a j)⟫_𝕜 := by
  change b.repr (T (a.repr.symm (lp.single 2 j 1))) i = _
  rw [a.repr_symm_single, b.repr_apply_apply]

end HilbertBasis
