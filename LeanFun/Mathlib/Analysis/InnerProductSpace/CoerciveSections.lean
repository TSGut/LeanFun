/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.CoerciveFiniteSection
public import LeanFun.Mathlib.Analysis.Normed.Operator.StableCompactPerturbation

/-! # Convergent coordinate sections of coercive operators plus compact perturbations

Reference: Böttcher–Silbermann, Introduction to Large Truncated Toeplitz
Matrices, finite section method. Invertibility of the full perturbed operator
is explicit; coercivity supplies stability of the unperturbed sections.
-/

@[expose] public noncomputable section
open ContinuousLinearMap Filter
open scoped Topology InnerProductSpace
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]
local notation "H" => lp (fun _ : ℕ ↦ 𝕜) 2

/-- Orthogonal coordinate sections converge strongly to their bounded operator. -/
theorem tendsto_coerciveFiniteSection (A : H →L[𝕜] H) (u : H) :
    Tendsto (fun N ↦ coerciveFiniteSection (initialL2Projection N) A u)
      atTop (𝓝 (A u)) := by
  have ht := tendsto_apply_of_strongly_tendsto_of_tendsto
    (fun N ↦ initialL2Projection (𝕜 := 𝕜) N) 1 norm_initialL2Projection_le
    tendsto_initialL2Projection ((A.continuous.tendsto u).comp (tendsto_initialL2Projection u))
  change Tendsto (fun N ↦ u-initialL2Projection N u+
    initialL2Projection N (A (initialL2Projection N u))) atTop (𝓝 (A u))
  simpa only [Function.comp_def, one_apply_eq_self, sub_self, zero_add] using
    ((tendsto_const_nhds (x := u)).sub (tendsto_initialL2Projection u)).add ht

/-- Compressing a sum separates its coercive section from the compact double section. -/
theorem coerciveFiniteSection_add (N : ℕ) (A K : H →L[𝕜] H) :
    coerciveFiniteSection (initialL2Projection N) (A+K) =
      coerciveFiniteSection (initialL2Projection N) A+
        (initialL2Projection N).comp (K.comp (initialL2Projection N)) := by
  simp only [coerciveFiniteSection, add_comp, comp_add, add_assoc]

/-- Every coercive coordinate section is invertible. -/
theorem isUnit_initialCoerciveFiniteSection (A : H →L[𝕜] H) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜) (N : ℕ) :
    IsUnit (coerciveFiniteSection (initialL2Projection N) A) :=
  isUnit_coerciveFiniteSection (initialL2Projection (𝕜 := 𝕜) N) A
    (adjoint_initialL2Projection N) (initialL2Projection_idempotent N) ha ha1 hA

/-- The inverses of coercive coordinate sections share a single norm bound. -/
theorem norm_inverse_initialCoerciveFiniteSection_le (A : H →L[𝕜] H) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜) (N : ℕ) :
    ‖Ring.inverse (coerciveFiniteSection (initialL2Projection N) A)‖ ≤ a⁻¹ :=
  norm_inverse_coerciveFiniteSection_le (initialL2Projection (𝕜 := 𝕜) N) A
    (adjoint_initialL2Projection N) (initialL2Projection_idempotent N) ha ha1 hA

/-- Coercive plus compact operators have eventually invertible coordinate sections. -/
theorem eventually_isUnit_coerciveFiniteSection_add_compact
    (A K : H →L[𝕜] H) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜)
    (hK : IsCompactOperator K) (hAK : IsUnit (A+K)) :
    ∀ᶠ N in atTop, IsUnit (coerciveFiniteSection (initialL2Projection N) (A+K)) := by
  simp_rw [coerciveFiniteSection_add]
  exact eventually_isUnit_add_compact_of_stable (𝕜 := 𝕜) (E := H) (C := a⁻¹)
    (fun N ↦ coerciveFiniteSection (initialL2Projection N) A) A
    (isUnit_initialCoerciveFiniteSection A ha ha1 hA)
    (isUnit_of_re_inner_le A ha hA)
    (norm_inverse_initialCoerciveFiniteSection_le A ha ha1 hA)
    (tendsto_coerciveFiniteSection A)
    (fun N ↦ (initialL2Projection N).comp (K.comp (initialL2Projection N))) K
    (tendsto_initialL2Sections_norm K hK) hK hAK

/-- Coercive plus compact coordinate solves converge for every ℓ² right-hand side. -/
theorem tendsto_coerciveFiniteSection_add_compact_solution
    (A K : H →L[𝕜] H) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜)
    (hK : IsCompactOperator K) (hAK : IsUnit (A+K)) (f : H) :
    Tendsto (fun N ↦ Ring.inverse (coerciveFiniteSection (initialL2Projection N) (A+K))
      (initialL2Projection N f)) atTop (𝓝 (Ring.inverse (A+K) f)) := by
  simp_rw [coerciveFiniteSection_add]
  exact tendsto_inverse_add_compact_apply_of_stable (𝕜 := 𝕜) (E := H) (C := a⁻¹)
    (fun N ↦ coerciveFiniteSection (initialL2Projection N) A) A
    (isUnit_initialCoerciveFiniteSection A ha ha1 hA)
    (isUnit_of_re_inner_le A ha hA)
    (norm_inverse_initialCoerciveFiniteSection_le A ha ha1 hA)
    (tendsto_coerciveFiniteSection A)
    (fun N ↦ (initialL2Projection N).comp (K.comp (initialL2Projection N))) K
    (tendsto_initialL2Sections_norm K hK) hK hAK
    (fun N ↦ initialL2Projection N f) f (tendsto_initialL2Projection f)

/-- The section inverse norms admit a bound independent of sufficiently large cutoffs. -/
theorem eventually_norm_inverse_coerciveFiniteSection_add_compact_le
    (A K : H →L[𝕜] H) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : ∀ u, a*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_𝕜)
    (hK : IsCompactOperator K) (hAK : IsUnit (A+K)) :
    ∀ᶠ N in atTop, ‖Ring.inverse (coerciveFiniteSection (initialL2Projection N) (A+K))‖ ≤
      (‖Ring.inverse (1+Ring.inverse A*K)‖+1)*a⁻¹ := by
  simp_rw [coerciveFiniteSection_add]
  exact eventually_norm_inverse_add_compact_le_of_stable (𝕜 := 𝕜) (E := H) (C := a⁻¹)
    (fun N ↦ coerciveFiniteSection (initialL2Projection N) A) A
    (isUnit_initialCoerciveFiniteSection A ha ha1 hA)
    (isUnit_of_re_inner_le A ha hA)
    (norm_inverse_initialCoerciveFiniteSection_le A ha ha1 hA)
    (tendsto_coerciveFiniteSection A)
    (fun N ↦ (initialL2Projection N).comp (K.comp (initialL2Projection N))) K
    (tendsto_initialL2Sections_norm K hK) hK hAK

/-- An invertible whole-space section gives the unique genuine projected solution. -/
theorem existsUnique_coerciveFiniteSection_solution (A : H →L[𝕜] H) (N : ℕ)
    (hA : IsUnit (coerciveFiniteSection (initialL2Projection N) A)) (f : H) :
    ∃! u, initialL2Projection N u = u ∧
      initialL2Projection N (A u) = initialL2Projection N f := by
  let P := initialL2Projection (𝕜 := 𝕜) N
  let u := Ring.inverse (coerciveFiniteSection P A) (P f)
  have hp (v : H) : P (P v) = P v :=
    congrArg (fun B : H →L[𝕜] H ↦ B v) (initialL2Projection_idempotent N)
  have he : u-P u+P (A (P u)) = P f := by
    have hh := congrArg (fun B : H →L[𝕜] H ↦ B (P f))
      (Ring.mul_inverse_cancel (coerciveFiniteSection P A) hA)
    simpa only [u, coerciveFiniteSection, mul_apply_eq_comp, add_apply, sub_apply,
      one_apply_eq_self, comp_apply] using hh
  have hpe : P (A (P u)) = P f := by
    have hh := congrArg P he
    simpa only [map_add, map_sub, hp, sub_self, zero_add] using hh
  have hu : P u = u := by
    rw [hpe] at he
    exact (sub_eq_zero.mp (add_eq_right.mp he)).symm
  refine ⟨u, ⟨hu, by simpa only [hu] using hpe⟩, ?_⟩
  intro v hv
  have hv' : coerciveFiniteSection P A v = P f := by
    change v-P v+P (A (P v)) = P f
    rw [hv.1, sub_self, zero_add, hv.2]
  have hi := congrArg (fun B : H →L[𝕜] H ↦ B v)
    (Ring.inverse_mul_cancel (coerciveFiniteSection P A) hA)
  simpa only [mul_apply_eq_comp, one_apply_eq_self, hv', u] using hi.symm

end lp
