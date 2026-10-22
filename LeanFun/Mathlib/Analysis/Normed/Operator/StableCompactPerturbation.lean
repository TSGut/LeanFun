/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Operator.FiniteSection
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Compact perturbations of strongly convergent stable operator families

Reference: the collectively compact approximation argument in
Böttcher–Silbermann, Introduction to Large Truncated Toeplitz Matrices.
-/

public noncomputable section
open Filter
open scoped Topology
namespace ContinuousLinearMap
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Uniformly bounded strong convergence also allows a convergent input sequence. -/
theorem tendsto_apply_of_strongly_tendsto_of_tendsto
    (A : ℕ → E →L[𝕜] E) (B : E →L[𝕜] E) {C : ℝ}
    (hC : ∀ n, ‖A n‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)))
    {x : ℕ → E} {y : E} (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n ↦ A n (x n)) atTop (𝓝 (B y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ show ‖A n (x n)-B y‖ ≤ C*‖x n-y‖+‖A n y-B y‖ from ?_) ?_
  · have he : A n (x n)-B y = A n (x n-y)+(A n y-B y) := by
      rw [map_sub]
      abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add
      ((A n).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))) le_rfl)
  · simpa using ((hx.sub (tendsto_const_nhds (x := y))).norm.const_mul C).add
      ((ht y).sub (tendsto_const_nhds (x := B y))).norm

omit [CompleteSpace E] in
/-- Uniformly bounded inverses turn strong operator convergence into strong inverse convergence. -/
theorem tendsto_inverse_apply_of_strongly_tendsto
    (A : ℕ → E →L[𝕜] E) (B : E →L[𝕜] E)
    (hA : ∀ n, IsUnit (A n)) (hB : IsUnit B) {C : ℝ}
    (hC : ∀ n, ‖Ring.inverse (A n)‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x))) (f : E) :
    Tendsto (fun n ↦ Ring.inverse (A n) f) atTop (𝓝 (Ring.inverse B f)) := by
  let x := Ring.inverse B f
  have hx : B x = f := by
    have h := congrArg (fun U : E →L[𝕜] E ↦ U f) (Ring.mul_inverse_cancel B hB)
    simpa only [x, mul_apply_eq_comp, one_apply_eq_self] using h
  have he (n : ℕ) : Ring.inverse (A n) f-x = Ring.inverse (A n) (B x-A n x) := by
    rw [hx, map_sub]
    have h := congrArg (fun U : E →L[𝕜] E ↦ U x) (Ring.inverse_mul_cancel (A n) (hA n))
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using congrArg (fun y ↦ Ring.inverse (A n) f-y) h.symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ show ‖Ring.inverse (A n) f-x‖ ≤ C*‖B x-A n x‖ from ?_) ?_
  · rw [he]
    exact (Ring.inverse (A n)).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
  · simpa using ((tendsto_const_nhds (x := B x)).sub (ht x)).norm.const_mul C

omit [CompleteSpace E] in
/-- Strong convergence with a uniform norm bound is uniform after a compact operator. -/
theorem tendsto_compact_comp_of_strongly_tendsto
    (A : ℕ → E →L[𝕜] E) (B : E →L[𝕜] E) {C : ℝ}
    (hC : ∀ n, ‖A n‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) :
    Tendsto (fun n ↦ (A n).comp K) atTop (𝓝 (B.comp K)) := by
  let P : ℕ → E →L[𝕜] E := fun n ↦ 1 + (A n-B)
  have hp : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x) := by
    intro x
    simpa only [P, add_apply, sub_apply, one_apply_eq_self, sub_self, add_zero] using
      (tendsto_const_nhds (x := x)).add ((ht x).sub (tendsto_const_nhds (x := B x)))
  have hb (n : ℕ) : ‖P n‖ ≤ 1+(C+‖B‖) := by
    apply (norm_add_le _ _).trans
    apply add_le_add norm_id_le
    exact (norm_sub_le _ _).trans (add_le_add (hC n) le_rfl)
  have h := tendsto_compact_comp_of_strongly_tendsto_id P hb hp K hK
  have he (n : ℕ) : (A n).comp K = (P n).comp K - K + B.comp K := by
    ext x
    simp only [P, comp_apply, add_apply, sub_apply, one_apply_eq_self]
    abel
  simp_rw [he]
  simpa using (h.sub (tendsto_const_nhds (x := K))).add (tendsto_const_nhds (x := B.comp K))

omit [CompleteSpace E] in
/-- Stable base inverses precondition a compact perturbation in operator norm. -/
theorem tendsto_inverse_comp_compact_of_strongly_tendsto
    (A : ℕ → E →L[𝕜] E) (B : E →L[𝕜] E)
    (hA : ∀ n, IsUnit (A n)) (hB : IsUnit B) {C : ℝ}
    (hC : ∀ n, ‖Ring.inverse (A n)‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) :
    Tendsto (fun n ↦ (Ring.inverse (A n)).comp K) atTop
      (𝓝 ((Ring.inverse B).comp K)) :=
  tendsto_compact_comp_of_strongly_tendsto _ _ hC
    (tendsto_inverse_apply_of_strongly_tendsto A B hA hB hC ht) K hK

omit [CompleteSpace E] in
/-- Strong convergence is uniform after norm-convergent compact-limit right factors. -/
theorem tendsto_comp_of_strongly_tendsto_of_tendsto_compact
    (A : ℕ → E →L[𝕜] E) (B : E →L[𝕜] E) {C : ℝ}
    (hC : ∀ n, ‖A n‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)))
    (K : ℕ → E →L[𝕜] E) (L : E →L[𝕜] E)
    (hK : Tendsto K atTop (𝓝 L)) (hL : IsCompactOperator L) :
    Tendsto (fun n ↦ (A n).comp (K n)) atTop (𝓝 (B.comp L)) := by
  have hz : Tendsto (fun n ↦ (A n).comp (K n-L)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun n ↦ show ‖(A n).comp (K n-L)‖ ≤ C*‖K n-L‖ from ?_) ?_
    · exact (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
    · simpa using (hK.sub (tendsto_const_nhds (x := L))).norm.const_mul C
  have he (n : ℕ) : (A n).comp (K n) = (A n).comp (K n-L)+(A n).comp L := by
    rw [comp_sub, sub_add_cancel]
  simp_rw [he]
  simpa using hz.add (tendsto_compact_comp_of_strongly_tendsto A B hC ht L hL)

/-- Stable base sections remain eventually invertible under a norm-convergent
compact perturbation when the limiting full operator is invertible. -/
theorem eventually_isUnit_add_compact_of_stable
    (A : ℕ → E →L[𝕜] E) (B : E →L[𝕜] E)
    (hA : ∀ n, IsUnit (A n)) (hB : IsUnit B) {C : ℝ}
    (hC : ∀ n, ‖Ring.inverse (A n)‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)))
    (K : ℕ → E →L[𝕜] E) (L : E →L[𝕜] E)
    (hK : Tendsto K atTop (𝓝 L)) (hL : IsCompactOperator L) (hBL : IsUnit (B+L)) :
    ∀ᶠ n in atTop, IsUnit (A n+K n) := by
  have he (U V : E →L[𝕜] E) (hU : IsUnit U) :
      U * (1+Ring.inverse U*V) = U+V := by
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel U hU, one_mul]
  have hd : IsUnit (1+Ring.inverse B*L) := by
    have := hB.ringInverse.mul hBL
    rwa [mul_add, Ring.inverse_mul_cancel B hB] at this
  have hh : Tendsto (fun n ↦ 1+Ring.inverse (A n)*K n) atTop
      (𝓝 (1+Ring.inverse B*L)) :=
    tendsto_const_nhds.add (tendsto_comp_of_strongly_tendsto_of_tendsto_compact
      _ _ hC (tendsto_inverse_apply_of_strongly_tendsto A B hA hB hC ht) K L hK hL)
  filter_upwards [eventually_isUnit_of_tendsto hh hd] with n hn
  rw [← he (A n) (K n) (hA n)]
  exact (hA n).mul hn

/-- The corresponding perturbed inverse solutions converge strongly. -/
theorem tendsto_inverse_add_compact_apply_of_stable
    (A : ℕ → E →L[𝕜] E) (B : E →L[𝕜] E)
    (hA : ∀ n, IsUnit (A n)) (hB : IsUnit B) {C : ℝ}
    (hC : ∀ n, ‖Ring.inverse (A n)‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)))
    (K : ℕ → E →L[𝕜] E) (L : E →L[𝕜] E)
    (hK : Tendsto K atTop (𝓝 L)) (hL : IsCompactOperator L)
    (hBL : IsUnit (B+L)) (f : ℕ → E) (g : E) (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n ↦ Ring.inverse (A n+K n) (f n)) atTop (𝓝 (Ring.inverse (B+L) g)) := by
  have he (U V : E →L[𝕜] E) (hU : IsUnit U) :
      Ring.inverse (U+V) = Ring.inverse (1+Ring.inverse U*V)*Ring.inverse U := by
    have hh : U+V = U*(1+Ring.inverse U*V) := by
      rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel U hU, one_mul]
    rw [hh, Ring.inverse_mul (Or.inl hU)]
  have hd : IsUnit (1+Ring.inverse B*L) := by
    have := hB.ringInverse.mul hBL
    rwa [mul_add, Ring.inverse_mul_cancel B hB] at this
  have hh : Tendsto (fun n ↦ 1+Ring.inverse (A n)*K n) atTop
      (𝓝 (1+Ring.inverse B*L)) :=
    tendsto_const_nhds.add (tendsto_comp_of_strongly_tendsto_of_tendsto_compact
      _ _ hC (tendsto_inverse_apply_of_strongly_tendsto A B hA hB hC ht) K L hK hL)
  simp_rw [he _ _ hB, he _ _ (hA _), mul_apply_eq_comp]
  have hc : Continuous (fun p : (E →L[𝕜] E) × E ↦ p.1 p.2) := by fun_prop
  exact hc.continuousAt.tendsto.comp ((tendsto_inverse_of_tendsto hh hd).prodMk_nhds
    (tendsto_apply_of_strongly_tendsto_of_tendsto _ _ hC
      (tendsto_inverse_apply_of_strongly_tendsto A B hA hB hC ht) hf))

/-- The perturbed inverse norms are eventually uniformly bounded. -/
theorem eventually_norm_inverse_add_compact_le_of_stable
    (A : ℕ → E →L[𝕜] E) (B : E →L[𝕜] E)
    (hA : ∀ n, IsUnit (A n)) (hB : IsUnit B) {C : ℝ}
    (hC : ∀ n, ‖Ring.inverse (A n)‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)))
    (K : ℕ → E →L[𝕜] E) (L : E →L[𝕜] E)
    (hK : Tendsto K atTop (𝓝 L)) (hL : IsCompactOperator L) (hBL : IsUnit (B+L)) :
    ∀ᶠ n in atTop, ‖Ring.inverse (A n+K n)‖ ≤
      (‖Ring.inverse (1+Ring.inverse B*L)‖+1)*C := by
  have hd : IsUnit (1+Ring.inverse B*L) := by
    have := hB.ringInverse.mul hBL
    rwa [mul_add, Ring.inverse_mul_cancel B hB] at this
  have hh : Tendsto (fun n ↦ 1+Ring.inverse (A n)*K n) atTop
      (𝓝 (1+Ring.inverse B*L)) :=
    tendsto_const_nhds.add (tendsto_comp_of_strongly_tendsto_of_tendsto_compact
      _ _ hC (tendsto_inverse_apply_of_strongly_tendsto A B hA hB hC ht) K L hK hL)
  filter_upwards [eventually_norm_inverse_le_of_tendsto hh hd] with n hn
  have he : A n+K n = A n*(1+Ring.inverse (A n)*K n) := by
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel _ (hA n), one_mul]
  rw [he, Ring.inverse_mul (Or.inl (hA n))]
  exact (norm_mul_le _ _).trans (mul_le_mul hn (hC n) (norm_nonneg _) (by positivity))

end ContinuousLinearMap
