/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Operator.SmallNormSolve

/-! # Quantitative perturbation of invertible operators

Reference: the Banach perturbation lemma, obtained by factoring out an
invertible reference operator and applying the Neumann series.
-/

public noncomputable section
open Filter
open scoped Topology
namespace ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Small preconditioned operator errors preserve invertibility. -/
theorem isUnit_of_inverse_norm_mul_sub_lt_one (A B : E →L[𝕜] E)
    (hA : IsUnit A) (h : ‖Ring.inverse A‖ * ‖A-B‖ < 1) : IsUnit B := by
  have ht : ‖Ring.inverse A * (A-B)‖ < 1 := (norm_mul_le _ _).trans_lt h
  have he : B = A * (1 - Ring.inverse A * (A-B)) := by
    rw [mul_sub, mul_one, ← mul_assoc, Ring.mul_inverse_cancel A hA, one_mul]
    abel
  rw [he]
  exact hA.mul (isUnit_one_sub_of_norm_lt_one ht)

/-- A quantitative inverse bound for perturbations of an invertible operator. -/
theorem norm_inverse_le_of_inverse_norm_mul_sub (A B : E →L[𝕜] E)
    (hA : IsUnit A) {r : ℝ} (hr : ‖Ring.inverse A‖ * ‖A-B‖ ≤ r) (hr1 : r < 1) :
    ‖Ring.inverse B‖ ≤ (1/(1-r))*‖Ring.inverse A‖ := by
  have he : B = A * (1 - Ring.inverse A * (A-B)) := by
    rw [mul_sub, mul_one, ← mul_assoc, Ring.mul_inverse_cancel A hA, one_mul]
    abel
  rw [he, Ring.inverse_mul (Or.inl hA)]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    (norm_inverse_one_sub_le _ ((norm_mul_le _ _).trans hr) hr1) (norm_nonneg _))

omit [CompleteSpace E] in
/-- Kernel/operator and right-hand-side errors enter the same residual bound. -/
theorem norm_inverse_solution_sub_le (A B : E →L[𝕜] E)
    (hB : IsUnit B) (u g : E) :
    ‖Ring.inverse B g-u‖ ≤ ‖Ring.inverse B‖ *
      (‖g-A u‖ + ‖A-B‖*‖u‖) := by
  rw [norm_sub_rev]
  apply (norm_sub_inverse_apply_le_residual B hB g u).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have he : B u-g = (A u-g)-(A-B) u := by
    simp only [sub_apply]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (by rw [norm_sub_rev]) ((A-B).le_opNorm u))

/-- Norm-small changes preserve an eventually stable family, with twice its inverse bound. -/
theorem eventually_stable_of_norm_sub_tendsto_zero
    (A B : ℕ → E →L[𝕜] E) {C : ℝ}
    (hA : ∀ᶠ n in atTop, IsUnit (A n) ∧ ‖Ring.inverse (A n)‖ ≤ C)
    (he : Tendsto (fun n ↦ ‖A n-B n‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, IsUnit (B n) ∧ ‖Ring.inverse (B n)‖ ≤ 2*C := by
  have ht : Tendsto (fun n ↦ C*‖A n-B n‖) atTop (𝓝 0) := by
    simpa using he.const_mul C
  filter_upwards [hA, (tendsto_order.mp ht).2 (1/2 : ℝ) (by norm_num)] with n hn heN
  have hb : ‖Ring.inverse (A n)‖*‖A n-B n‖ ≤ (1/2 : ℝ) :=
    (mul_le_mul_of_nonneg_right hn.2 (norm_nonneg _)).trans heN.le
  refine ⟨isUnit_of_inverse_norm_mul_sub_lt_one _ _ hn.1 (hb.trans_lt (by norm_num)), ?_⟩
  have hh := norm_inverse_le_of_inverse_norm_mul_sub (A n) (B n) hn.1 hb (by norm_num)
  norm_num at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hn.2 (by norm_num))

omit [CompleteSpace E] in
/-- Stable, strongly consistent operators solve convergent varying data. -/
theorem tendsto_inverse_apply_of_eventually_stable
    (B : ℕ → E →L[𝕜] E) {C : ℝ}
    (hB : ∀ᶠ n in atTop, IsUnit (B n) ∧ ‖Ring.inverse (B n)‖ ≤ C)
    (u : E) (g : ℕ → E)
    (he : Tendsto (fun n ↦ g n-B n u) atTop (𝓝 0)) :
    Tendsto (fun n ↦ Ring.inverse (B n) (g n)) atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_
    (by simpa using he.norm.const_mul C)
  filter_upwards [hB] with n hn
  rw [norm_sub_rev]
  exact (norm_sub_inverse_apply_le_residual _ hn.1 _ _).trans
    (by rw [norm_sub_rev (B n u)]; exact
      mul_le_mul_of_nonneg_right hn.2 (norm_nonneg _))

end ContinuousLinearMap
