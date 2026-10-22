/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.Shift

/-! # Bounded Toeplitz operators on the one-sided ℓ² space

A bounded operator is Toeplitz when its matrix is constant along diagonals.
Equivalently it is fixed by `T ↦ S* T S`, where `S` is the unilateral shift.
This definition does not assume a finite-band or polynomial symbol.
Reference: Böttcher–Silbermann, Introduction to Large Truncated Toeplitz Matrices.
-/

@[expose] public noncomputable section
open Filter ContinuousLinearMap
open scoped Topology
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]
local notation "H" => lp (fun _ : ℕ ↦ 𝕜) 2

/-- A bounded operator on ℓ² is determined by its coordinate columns. -/
theorem continuousLinearMap_ext_single {T U : H →L[𝕜] H}
    (h : ∀ n, T (lp.single 2 n 1) = U (lp.single 2 n 1)) : T = U := by
  have hs (n : ℕ) (a : 𝕜) : T (lp.single 2 n a) = U (lp.single 2 n a) := by
    have he : lp.single 2 n a = a • (lp.single 2 n (1 : 𝕜) : H) := by
      rw [← lp.single_smul]
      simp
    rw [he, map_smul, map_smul, h]
  apply ContinuousLinearMap.ext
  intro u
  have he (N : ℕ) : T (initialL2Projection N u) = U (initialL2Projection N u) := by
    simp only [initialL2Projection_apply, map_sum, hs]
  have ht := (T.continuous.tendsto u).comp (tendsto_initialL2Projection u)
  have hu := (U.continuous.tendsto u).comp (tendsto_initialL2Projection u)
  exact tendsto_nhds_unique ht (by simpa only [Function.comp_def, he] using hu)

/-- Bounded Toeplitz operators have constant matrix diagonals. -/
def IsToeplitz (T : H →L[𝕜] H) : Prop :=
  ∀ i j : ℕ, T (lp.single 2 (j+1) 1) (i+1) = T (lp.single 2 j 1) i

/-- Matrix diagonal invariance is equivalent to the shift sandwich identity. -/
theorem isToeplitz_iff_shift (T : H →L[𝕜] H) :
    IsToeplitz T ↔ backwardShiftL2.comp (T.comp forwardShiftL2.toContinuousLinearMap) = T := by
  constructor
  · intro h
    apply continuousLinearMap_ext_single
    intro j
    apply lp.ext
    funext i
    simpa only [comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      forwardShiftL2_single, backwardShiftL2_apply] using h i j
  · intro h i j
    have he := congrArg (fun U : H →L[𝕜] H ↦ U (lp.single 2 j 1) i) h
    simpa only [comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      forwardShiftL2_single, backwardShiftL2_apply] using he

/-- The bounded Toeplitz operators form a linear subspace of bounded operators. -/
def toeplitzSubmodule : Submodule 𝕜 (H →L[𝕜] H) where
  carrier := {T | IsToeplitz T}
  zero_mem' := by intro i j; simp
  add_mem' {T U} hT hU := by
    intro i j
    simp only [add_apply, lp.coeFn_add, Pi.add_apply, hT i j, hU i j]
  smul_mem' c T hT := by
    intro i j
    simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply, hT i j]

/-- Toeplitz structure is preserved under operator-norm limits. -/
theorem isClosed_isToeplitz : IsClosed {T : H →L[𝕜] H | IsToeplitz T} := by
  have he : {T : H →L[𝕜] H | IsToeplitz T} =
      ⋂ i : ℕ, ⋂ j : ℕ, {T | T (lp.single 2 (j+1) 1) (i+1) = T (lp.single 2 j 1) i} := by
    ext T
    simp [IsToeplitz]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq
    ((lp.evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 (i+1)).continuous.comp (by fun_prop))
    ((lp.evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i).continuous.comp (by fun_prop))

/-- The identity is Toeplitz. -/
theorem isToeplitz_one : IsToeplitz (1 : H →L[𝕜] H) := by
  rw [isToeplitz_iff_shift]
  change backwardShiftL2.comp forwardShiftL2.toContinuousLinearMap = (1 : H →L[𝕜] H)
  exact backwardShiftL2_comp_forwardShiftL2

/-- The forward shift is Toeplitz. -/
theorem isToeplitz_forwardShiftL2 : IsToeplitz (forwardShiftL2 (𝕜 := 𝕜)).toContinuousLinearMap := by
  rw [isToeplitz_iff_shift, ← comp_assoc, backwardShiftL2_comp_forwardShiftL2]
  rfl

/-- The backward shift is Toeplitz. -/
theorem isToeplitz_backwardShiftL2 : IsToeplitz (backwardShiftL2 (𝕜 := 𝕜)) := by
  rw [isToeplitz_iff_shift, backwardShiftL2_comp_forwardShiftL2]
  rfl

/-- Taking the Hilbert adjoint preserves Toeplitz structure. -/
theorem IsToeplitz.adjoint {T : H →L[𝕜] H} (h : IsToeplitz T) :
    IsToeplitz T.adjoint := by
  rw [isToeplitz_iff_shift] at h ⊢
  have he := congrArg ContinuousLinearMap.adjoint h
  simpa only [adjoint_comp, backwardShiftL2, adjoint_adjoint, comp_assoc] using he

/-- Every nonnegative power of the forward shift is Toeplitz. -/
theorem isToeplitz_forwardShiftL2_pow (n : ℕ) :
    IsToeplitz ((forwardShiftL2 (𝕜 := 𝕜)).toContinuousLinearMap ^ n) := by
  rw [isToeplitz_iff_shift]
  change backwardShiftL2 * (forwardShiftL2.toContinuousLinearMap ^ n *
    forwardShiftL2.toContinuousLinearMap) = _
  rw [← pow_succ, pow_succ', ← mul_assoc]
  have h : backwardShiftL2 * (forwardShiftL2 (𝕜 := 𝕜)).toContinuousLinearMap = 1 :=
    backwardShiftL2_comp_forwardShiftL2
  rw [h, one_mul]

/-- Every nonnegative power of the backward shift is Toeplitz. -/
theorem isToeplitz_backwardShiftL2_pow (n : ℕ) :
    IsToeplitz ((backwardShiftL2 (𝕜 := 𝕜)) ^ n) := by
  rw [isToeplitz_iff_shift]
  change backwardShiftL2 * (backwardShiftL2 ^ n *
    forwardShiftL2.toContinuousLinearMap) = _
  rw [← mul_assoc, ← pow_succ', pow_succ, mul_assoc]
  have h : backwardShiftL2 * (forwardShiftL2 (𝕜 := 𝕜)).toContinuousLinearMap = 1 :=
    backwardShiftL2_comp_forwardShiftL2
  rw [h, mul_one]

end lp
