/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Order.Real
/-! # Smooth cutoffs of a vanishing boundary factor

The function `boundaryFactor a r = r * smoothTransition (a*r-1)` cuts off a
linearly vanishing factor before the boundary. Its derivative is uniformly
bounded in the scale `a`, and it agrees with the original factor away from
the boundary layer. This is the elementary cutoff estimate used in the
standard smooth-density proof for zero-boundary Sobolev spaces.
Reference: Evans, *Partial Differential Equations*, Chapter 5.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Real
private theorem transition_deriv_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have h : smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact smoothTransition.zero_of_nonpos hy.le
    simpa using h.deriv_eq
  · have h : smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact smoothTransition.one_of_one_le hy.le
    simpa using h.deriv_eq

/-- The smooth transition has bounded derivative and a bounded scaled transition derivative. -/
theorem exists_transition_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧
    (∀ x, |deriv smoothTransition x| ≤ M) ∧
    (∀ x, |x * deriv smoothTransition (x-1)| ≤ 2*M) := by
  have hc : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  let M := max C 0
  have hm : 0 ≤ M := le_max_right _ _
  have hd (x : ℝ) : |deriv smoothTransition x| ≤ M := by
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · exact (hC x hx).trans (le_max_left _ _)
    · rw [transition_deriv_zero (by simpa only [mem_Icc, not_and_or, not_le] using hx), abs_zero]
      exact hm
  refine ⟨M,hm,hd,fun x ↦ ?_⟩
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · rw [abs_mul]
    have hx0 : 0 ≤ x := le_trans zero_le_one hx.1
    have hxabs : |x| ≤ 2 := by simpa only [abs_of_nonneg hx0] using hx.2
    exact mul_le_mul hxabs (hd (x-1)) (abs_nonneg _) (by norm_num)
  · rw [transition_deriv_zero (by
      rcases lt_or_gt_of_ne (show x ≠ 1 by intro h; subst x; simp at hx) with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by simp only [mem_Icc, not_and_or, not_le] at hx; rcases hx with hx | hx <;> linarith)),
      mul_zero, abs_zero]
    positivity

/-- A smooth cutoff of a linearly vanishing factor at scale a. -/
def boundaryFactor (a r : ℝ) : ℝ := r * smoothTransition (a*r-1)

/-- The cutoff boundary factor is smooth. -/
theorem boundaryFactor_contDiff (a : ℝ) : ContDiff ℝ ∞ (boundaryFactor a) := by
  unfold boundaryFactor
  exact contDiff_id.mul (smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

/-- The derivative of the cutoff boundary factor. -/
theorem hasDerivAt_boundaryFactor (a r : ℝ) : HasDerivAt (boundaryFactor a)
    (smoothTransition (a*r-1) + (a*r)*deriv smoothTransition (a*r-1)) r := by
  have ht : HasDerivAt smoothTransition (deriv smoothTransition (a*r-1)) (a*r-1) := ((smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt
  unfold boundaryFactor
  convert (hasDerivAt_id r).mul
    (ht.comp r (((hasDerivAt_id r).const_mul a).sub_const 1)) using 1
  · rfl
  · simp only [one_mul, mul_one, Function.comp_apply, id_eq]
    ring

/-- Cutting off does not increase the absolute value of the boundary factor. -/
theorem abs_boundaryFactor_le (a r : ℝ) : |boundaryFactor a r| ≤ |r| := by
  rw [boundaryFactor, abs_mul, abs_of_nonneg (smoothTransition.nonneg _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (smoothTransition.le_one _)

/-- The derivative bound is independent of the cutoff scale. -/
theorem abs_deriv_boundaryFactor_le {M : ℝ}
    (hM : ∀ x, |x * deriv smoothTransition (x-1)| ≤ 2*M) (a r : ℝ) :
    |deriv (boundaryFactor a) r| ≤ 1+2*M := by
  rw [(hasDerivAt_boundaryFactor a r).deriv]
  exact (abs_add_le _ _).trans (add_le_add
    (by rw [abs_of_nonneg (smoothTransition.nonneg _)]; exact smoothTransition.le_one _) (hM (a*r)))

/-- The cutoff factor vanishes in the boundary layer. -/
theorem boundaryFactor_zero {a r : ℝ} (h : a*r ≤ 1) : boundaryFactor a r = 0 := by
  rw [boundaryFactor, smoothTransition.zero_of_nonpos (by linarith), mul_zero]

/-- Outside the transition layer the cutoff equals the original factor. -/
theorem boundaryFactor_eq {a r : ℝ} (h : 2 ≤ a*r) : boundaryFactor a r = r := by
  rw [boundaryFactor, smoothTransition.one_of_one_le (by linarith), mul_one]

/-- Outside the transition layer the cutoff derivative equals one. -/
theorem deriv_boundaryFactor_eq {a r : ℝ} (h : 2 < a*r) :
    deriv (boundaryFactor a) r = 1 := by
  rw [(hasDerivAt_boundaryFactor a r).deriv,
    smoothTransition.one_of_one_le (by linarith),
    transition_deriv_zero (Or.inr (by linarith)), mul_zero, add_zero]
end Real
