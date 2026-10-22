/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.CompactSections
public import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Coercive finite sections

Orthogonal compression preserves a positive real-part lower bound. The
identity on unresolved coordinates makes this a whole-space invertibility
statement. Reference: Böttcher–Silbermann, Introduction to Large Truncated
Toeplitz Matrices, finite section method.
-/

@[expose] public noncomputable section
open scoped InnerProductSpace NNReal
namespace ContinuousLinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Orthogonal compression with the identity on the unresolved complement. -/
def coerciveFiniteSection (P A : E →L[𝕜] E) : E →L[𝕜] E :=
  1-P+P.comp (A.comp P)

/-- The compressed quadratic form splits into a complement norm and a resolved form. -/
theorem inner_coerciveFiniteSection (P A : E →L[𝕜] E)
    (hP : P.adjoint = P) (hPP : P.comp P = P) (u : E) :
    ⟪u, coerciveFiniteSection P A u⟫_𝕜 =
      (‖u-P u‖^2 : ℝ) + ⟪P u, A (P u)⟫_𝕜 := by
  have hid : P (P u) = P u := congrArg (fun B : E →L[𝕜] E ↦ B u) hPP
  have hs (v w : E) : ⟪v, P w⟫_𝕜 = ⟪P v, w⟫_𝕜 := by
    simpa only [hP] using adjoint_inner_right P v w
  have hz : ⟪P u, u-P u⟫_𝕜 = 0 := by
    rw [← hs, map_sub, hid, sub_self, inner_zero_right]
  have he : ⟪u, u-P u⟫_𝕜 = (‖u-P u‖^2 : ℝ) := by
    calc
      _ = ⟪u-P u+P u, u-P u⟫_𝕜 := by rw [sub_add_cancel]
      _ = _ := by rw [inner_add_left, hz, add_zero, inner_self_eq_norm_sq_to_K]; simp
  change ⟪u, u-P u+P (A (P u))⟫_𝕜 = _
  rw [inner_add_right, he, hs]

/-- A positive lower bound survives orthogonal finite sections. -/
theorem re_inner_coerciveFiniteSection_le (P A : E →L[𝕜] E)
    (hP : P.adjoint = P) (hPP : P.comp P = P) {a : ℝ} (ha : a ≤ 1)
    (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜) (u : E) :
    a*‖u‖^2 ≤ RCLike.re ⟪u, coerciveFiniteSection P A u⟫_𝕜 := by
  have hid : P (P u) = P u := congrArg (fun B : E →L[𝕜] E ↦ B u) hPP
  have hz : ⟪u-P u, P u⟫_𝕜 = 0 := by
    rw [← hP, adjoint_inner_right, hP, map_sub, hid, sub_self, inner_zero_left]
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (u-P u) (P u) hz
  rw [sub_add_cancel] at hn
  rw [inner_coerciveFiniteSection P A hP hPP, map_add, RCLike.ofReal_re]
  have hb := hA (P u)
  nlinarith [sq_nonneg ‖u-P u‖]

/-- A uniformly positive real quadratic form gives an invertible bounded operator. -/
theorem isUnit_of_re_inner_le (A : E →L[𝕜] E) {a : ℝ} (ha : 0 < a)
    (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜) : IsUnit A := by
  apply isUnit_of_forall_le_norm_inner_map _ (c := ⟨a, ha.le⟩) ha
  intro u
  change ‖u‖^2*a ≤ ‖⟪A u, u⟫_𝕜‖
  rw [norm_inner_symm, mul_comm]
  exact (hA u).trans (RCLike.re_le_norm _)

/-- Uniform coercivity gives invertibility of every compressed section. -/
theorem isUnit_coerciveFiniteSection (P A : E →L[𝕜] E)
    (hP : P.adjoint = P) (hPP : P.comp P = P) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜) :
    IsUnit (coerciveFiniteSection P A) := by
  apply isUnit_of_forall_le_norm_inner_map _ (c := ⟨a, ha.le⟩) ha
  intro u
  change ‖u‖^2*a ≤ ‖⟪coerciveFiniteSection P A u, u⟫_𝕜‖
  rw [norm_inner_symm, mul_comm]
  exact (re_inner_coerciveFiniteSection_le P A hP hPP ha1 hA u).trans
    (RCLike.re_le_norm _)

omit [CompleteSpace E] in
/-- A coercive invertible operator has inverse norm at most the reciprocal lower bound. -/
theorem norm_inverse_le_of_re_inner_le (A : E →L[𝕜] E) (hunit : IsUnit A)
    {a : ℝ} (ha : 0 < a) (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜) :
    ‖Ring.inverse A‖ ≤ a⁻¹ := by
  have hlow : ∀ u, ‖u‖^2*(⟨a, ha.le⟩ : ℝ≥0) ≤ ‖⟪A u, u⟫_𝕜‖ := by
    intro u
    change ‖u‖^2*a ≤ ‖⟪A u, u⟫_𝕜‖
    rw [norm_inner_symm, mul_comm]
    exact (hA u).trans (RCLike.re_le_norm _)
  have hb := antilipschitz_of_forall_le_inner_map A (c := ⟨a, ha.le⟩) ha hlow
  apply opNorm_le_bound _ (inv_nonneg.mpr ha.le)
  intro u
  have he : A (Ring.inverse A u) = u := by
    have h := congrArg (fun U : E →L[𝕜] E ↦ U u) (Ring.mul_inverse_cancel A hunit)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  have h := hb.le_mul_dist (Ring.inverse A u) 0
  simp only [dist_zero_right, map_zero, he] at h
  change ‖Ring.inverse A u‖ ≤ a⁻¹*‖u‖ at h
  exact h

/-- Every orthogonal section shares the same inverse bound. -/
theorem norm_inverse_coerciveFiniteSection_le (P A : E →L[𝕜] E)
    (hP : P.adjoint = P) (hPP : P.comp P = P) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜) :
    ‖Ring.inverse (coerciveFiniteSection P A)‖ ≤ a⁻¹ :=
  norm_inverse_le_of_re_inner_le _ (isUnit_coerciveFiniteSection P A hP hPP ha ha1 hA)
    ha (re_inner_coerciveFiniteSection_le P A hP hPP ha1 hA)

end ContinuousLinearMap
