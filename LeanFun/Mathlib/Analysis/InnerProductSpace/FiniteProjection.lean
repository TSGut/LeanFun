/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Linarith

/-!
# Best approximation by finite orthonormal expansions

The estimates do not require completeness or a Hilbert basis. They apply to
finite orthogonal polynomial projections over both real and complex scalars.
Reference: the Hilbert-space best-approximation theorem; DLMF 18.2(viii).
-/

public section
open scoped InnerProductSpace
variable {𝕂 E ι : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [InnerProductSpace 𝕂 E]

/-- The residual of a finite orthonormal expansion is orthogonal to every
linear combination of the selected vectors. -/
theorem Orthonormal.inner_sub_sum_inner_sum_eq_zero {v : ι → E}
    (hv : Orthonormal 𝕂 v) (s : Finset ι) (x : E) (c : ι → 𝕂) :
    inner 𝕂 (x - ∑ i ∈ s, inner 𝕂 (v i) x • v i) (∑ i ∈ s, c i • v i) = 0 := by
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inner_smul_right]
  have h : inner 𝕂 (v i) (x - ∑ j ∈ s, inner 𝕂 (v j) x • v j) = 0 := by
    rw [inner_sub_right, hv.inner_right_sum _ hi, sub_self]
  rw [inner_eq_zero_symm.mp h, mul_zero]

/-- Orthogonal coefficients minimise the error among all combinations of a
fixed finite orthonormal family (Hilbert-space best approximation). -/
theorem Orthonormal.norm_sub_sum_inner_le {v : ι → E} (hv : Orthonormal 𝕂 v)
    (s : Finset ι) (x : E) (c : ι → 𝕂) :
    ‖x - ∑ i ∈ s, inner 𝕂 (v i) x • v i‖ ≤ ‖x - ∑ i ∈ s, c i • v i‖ := by
  let a := ∑ i ∈ s, inner 𝕂 (v i) x • v i
  let b := ∑ i ∈ s, c i • v i
  have ho : inner 𝕂 (x - a) (a - b) = 0 := by
    rw [inner_sub_right, hv.inner_sub_sum_inner_sum_eq_zero s x,
      hv.inner_sub_sum_inner_sum_eq_zero s x, sub_self]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - a) (a - b) ho
  rw [sub_add_sub_cancel] at hp
  change ‖x - a‖ ≤ ‖x - b‖
  nlinarith [norm_nonneg (x - a), norm_nonneg (x - b), sq_nonneg ‖a - b‖]

/-- A finite orthogonal projection cannot increase the residual norm. -/
theorem Orthonormal.norm_sub_sum_inner_le_norm {v : ι → E} (hv : Orthonormal 𝕂 v)
    (s : Finset ι) (x : E) :
    ‖x - ∑ i ∈ s, inner 𝕂 (v i) x • v i‖ ≤ ‖x‖ := by
  simpa using hv.norm_sub_sum_inner_le s x (fun _ ↦ (0 : 𝕂))

/-- Best approximation holds for every vector in the selected span, without
choosing coordinates for the competitor. -/
theorem Orthonormal.norm_sub_sum_inner_le_of_mem_span {v : ι → E}
    (hv : Orthonormal 𝕂 v) (s : Finset ι) (x y : E)
    (hy : y ∈ Submodule.span 𝕂 (v '' (s : Set ι))) :
    ‖x - ∑ i ∈ s, inner 𝕂 (v i) x • v i‖ ≤ ‖x - y‖ := by
  let a := ∑ i ∈ s, inner 𝕂 (v i) x • v i
  have ho : inner 𝕂 (x - a) y = 0 := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      apply inner_eq_zero_symm.mp
      rw [inner_sub_right, hv.inner_right_sum _ hi, sub_self]
    | zero => simp
    | add u w _ _ hu hw => rw [inner_add_right, hu, hw, add_zero]
    | smul c u _ hu => rw [inner_smul_right, hu, mul_zero]
  have ha : inner 𝕂 (x - a) (a - y) = 0 := by
    rw [inner_sub_right, hv.inner_sub_sum_inner_sum_eq_zero s x, ho, sub_self]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - a) (a - y) ha
  rw [sub_add_sub_cancel] at hp
  change ‖x - a‖ ≤ ‖x - y‖
  nlinarith [norm_nonneg (x - a), norm_nonneg (x - y), sq_nonneg ‖a - y‖]

/-- A finite orthonormal projection fixes its selected span. -/
theorem Orthonormal.sum_inner_smul_eq_of_mem_span {v : ι → E}
    (hv : Orthonormal 𝕂 v) (s : Finset ι) (x : E)
    (hx : x ∈ Submodule.span 𝕂 (v '' (s : Set ι))) :
    ∑ i ∈ s, inner 𝕂 (v i) x • v i = x := by
  have h := hv.norm_sub_sum_inner_le_of_mem_span s x x hx
  rw [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at h
  exact h.symm

/-- Finite orthonormal projection has operator norm at most one. -/
theorem Orthonormal.norm_sum_inner_smul_le {v : ι → E}
    (hv : Orthonormal 𝕂 v) (s : Finset ι) (x : E) :
    ‖∑ i ∈ s, inner 𝕂 (v i) x • v i‖ ≤ ‖x‖ := by
  let a := ∑ i ∈ s, inner 𝕂 (v i) x • v i
  have ho : inner 𝕂 (x - a) a = 0 := hv.inner_sub_sum_inner_sum_eq_zero s x _
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - a) a ho
  rw [sub_add_cancel] at hp
  change ‖a‖ ≤ ‖x‖
  nlinarith [norm_nonneg x, norm_nonneg a, sq_nonneg ‖x - a‖]
