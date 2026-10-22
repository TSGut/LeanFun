/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.CoerciveSections
public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.PositiveSymbol
public import LeanFun.Mathlib.Analysis.Normed.Operator.CompactInjective

/-! # Stable sections of continuous Toeplitz operators plus compact corrections

Symbols with uniformly positive real part have stable orthogonal sections.
An invertible compact perturbation retains eventual stability and convergence.
Reference: Böttcher–Silbermann, Introduction to Large Truncated Toeplitz Matrices.
-/

@[expose] public noncomputable section
open ContinuousLinearMap Filter
open scoped Topology InnerProductSpace
namespace AddCircle
variable {T : ℝ} [Fact (0 < T)]
local notation "H" => lp (fun _ : ℕ ↦ ℂ) 2

/-- Injectivity is the remaining obligation for a compact perturbation of a positive symbol. -/
theorem isUnit_continuousToeplitz_add_of_injective (f : C(AddCircle T, ℂ))
    (K : H →L[ℂ] H) {a : ℝ} (ha : 0 < a) (hf : ∀ x, a ≤ (f x).re)
    (hK : IsCompactOperator K) (hinj : Function.Injective (continuousToeplitz f+K)) :
    IsUnit (continuousToeplitz f+K) :=
  isUnit_add_of_injective_of_compact _ K
    (isUnit_continuousToeplitz_of_re_pos f ha hf) hK hinj

/-- Normalize a positive symbol lower bound to at most one for the complement identity. -/
theorem re_inner_continuousToeplitz_min_le (f : C(AddCircle T, ℂ)) {a : ℝ}
    (hf : ∀ x, a ≤ (f x).re) (u : H) :
    min a 1*‖u‖^2 ≤ RCLike.re ⟪u, continuousToeplitz f u⟫_ℂ :=
  (mul_le_mul_of_nonneg_right (min_le_left a 1) (sq_nonneg ‖u‖)).trans
    (re_inner_continuousToeplitz_le f hf u)

/-- An invertible Toeplitz-plus-compact operator with positive symbol real part
has eventually invertible leading sections. -/
theorem eventually_isUnit_continuousToeplitz_section (f : C(AddCircle T, ℂ))
    (K : H →L[ℂ] H) {a : ℝ} (ha : 0 < a) (hf : ∀ x, a ≤ (f x).re)
    (hK : IsCompactOperator K) (hunit : IsUnit (continuousToeplitz f+K)) :
    ∀ᶠ N in atTop, IsUnit (coerciveFiniteSection (lp.initialL2Projection N)
      (continuousToeplitz f+K)) :=
  lp.eventually_isUnit_coerciveFiniteSection_add_compact _ K
    (lt_min ha zero_lt_one) (min_le_right a 1)
    (re_inner_continuousToeplitz_min_le f hf) hK hunit

/-- The leading-section inverse norms are eventually bounded uniformly in the cutoff. -/
theorem eventually_norm_inverse_continuousToeplitz_section_le (f : C(AddCircle T, ℂ))
    (K : H →L[ℂ] H) {a : ℝ} (ha : 0 < a) (hf : ∀ x, a ≤ (f x).re)
    (hK : IsCompactOperator K) (hunit : IsUnit (continuousToeplitz f+K)) :
    ∀ᶠ N in atTop, ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
      (continuousToeplitz f+K))‖ ≤
      (‖Ring.inverse (1+Ring.inverse (continuousToeplitz f)*K)‖+1)*(min a 1)⁻¹ :=
  lp.eventually_norm_inverse_coerciveFiniteSection_add_compact_le _ K
    (lt_min ha zero_lt_one) (min_le_right a 1)
    (re_inner_continuousToeplitz_min_le f hf) hK hunit

/-- Leading-section solutions converge in ℓ² for every right-hand side. -/
theorem tendsto_continuousToeplitz_section_solution (f : C(AddCircle T, ℂ))
    (K : H →L[ℂ] H) {a : ℝ} (ha : 0 < a) (hf : ∀ x, a ≤ (f x).re)
    (hK : IsCompactOperator K) (hunit : IsUnit (continuousToeplitz f+K)) (g : H) :
    Tendsto (fun N ↦ Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
      (continuousToeplitz f+K)) (lp.initialL2Projection N g)) atTop
      (𝓝 (Ring.inverse (continuousToeplitz f+K) g)) :=
  lp.tendsto_coerciveFiniteSection_add_compact_solution _ K
    (lt_min ha zero_lt_one) (min_le_right a 1)
    (re_inner_continuousToeplitz_min_le f hf) hK hunit g

/-- The convergent sections are genuine uniquely solvable projected equations. -/
theorem eventually_existsUnique_continuousToeplitz_section_solution (f : C(AddCircle T, ℂ))
    (K : H →L[ℂ] H) {a : ℝ} (ha : 0 < a) (hf : ∀ x, a ≤ (f x).re)
    (hK : IsCompactOperator K) (hunit : IsUnit (continuousToeplitz f+K)) (g : H) :
    ∀ᶠ N in atTop, ∃! u, lp.initialL2Projection N u = u ∧
      lp.initialL2Projection N ((continuousToeplitz f+K) u) = lp.initialL2Projection N g := by
  filter_upwards [eventually_isUnit_continuousToeplitz_section f K ha hf hK hunit] with N hN
  exact lp.existsUnique_coerciveFiniteSection_solution _ N hN g

end AddCircle
