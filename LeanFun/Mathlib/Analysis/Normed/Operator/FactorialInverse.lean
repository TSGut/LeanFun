/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Operator.FiniteSection
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Inversion from factorial bounds on iterates

The Volterra resolvent argument needs decay of iterates, rather than a small
operator norm. A factorial majorant gives a norm-convergent Neumann series.
Reference: the successive-approximation proof for Volterra equations of the
second kind (Gutleb–Olver, arXiv:1906.03907, Section 3).
-/

public noncomputable section
open Filter
open scoped Topology
namespace ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A factorial bound on powers makes the operator Neumann series summable. -/
theorem summable_pow_of_factorial_bound (T : E →L[𝕜] E) {C M : ℝ}
    (h : ∀ n : ℕ, ‖T ^ n‖ ≤ C * (M ^ n / n.factorial)) :
    Summable (fun n : ℕ ↦ T ^ n) :=
  Summable.of_norm_bounded ((Real.summable_pow_div_factorial M).mul_left C) h

omit [CompleteSpace E] in
/-- Summable iterates give an inverse without assuming that the operator norm is less than one. -/
theorem isUnit_one_sub_of_summable_pow (T : E →L[𝕜] E)
    (h : Summable (fun n : ℕ ↦ T ^ n)) : IsUnit (1 - T) := by
  exact ⟨⟨1 - T, ∑' n : ℕ, T ^ n, h.one_sub_mul_tsum_pow,
    h.tsum_pow_mul_one_sub⟩, rfl⟩

omit [CompleteSpace E] in
/-- The resolvent is the norm-convergent series of iterates. -/
theorem inverse_one_sub_eq_tsum_pow (T : E →L[𝕜] E)
    (h : Summable (fun n : ℕ ↦ T ^ n)) :
    Ring.inverse (1 - T) = ∑' n : ℕ, T ^ n := by
  have hi := Ring.inverse_mul_cancel (1 - T) (isUnit_one_sub_of_summable_pow T h)
  calc
    _ = Ring.inverse (1 - T) * ((1 - T) * ∑' n : ℕ, T ^ n) := by
      rw [h.one_sub_mul_tsum_pow, mul_one]
    _ = _ := by rw [← mul_assoc, hi, one_mul]

/-- A factorial iterate bound implies invertibility of the second-kind equation. -/
theorem isUnit_one_sub_of_factorial_bound (T : E →L[𝕜] E) {C M : ℝ}
    (h : ∀ n : ℕ, ‖T ^ n‖ ≤ C * (M ^ n / n.factorial)) : IsUnit (1 - T) :=
  isUnit_one_sub_of_summable_pow T (summable_pow_of_factorial_bound T h)

omit [CompleteSpace E] in
/-- Every right-hand side has a unique solution when the iterate series is summable. -/
theorem existsUnique_sub_apply_eq_of_summable_pow (T : E →L[𝕜] E)
    (h : Summable (fun n : ℕ ↦ T ^ n)) (f : E) : ∃! u : E, u - T u = f := by
  have hu := isUnit_one_sub_of_summable_pow T h
  refine ⟨Ring.inverse (1 - T) f, ?_, ?_⟩
  · have he := congrArg (fun A : E →L[𝕜] E ↦ A f) (Ring.mul_inverse_cancel _ hu)
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] using he
  · intro u he
    have hi := congrArg (fun A : E →L[𝕜] E ↦ A u) (Ring.inverse_mul_cancel _ hu)
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, he] using hi.symm

end ContinuousLinearMap
