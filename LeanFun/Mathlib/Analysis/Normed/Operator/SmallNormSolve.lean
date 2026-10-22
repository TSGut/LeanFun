/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Operator.FiniteSection
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-! # Small-norm solves and residual error bounds

Contraction bounds give stable projected equations at every resolution without
compactness. A full residual gives an a posteriori error certificate.
Reference: the Neumann series and the Banach perturbation lemma.
-/

public noncomputable section
open Filter
open scoped Topology
namespace ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Quantitative inverse bound for a perturbation of norm at most `q < 1`. -/
theorem norm_inverse_one_sub_le (T : E →L[𝕜] E) {q : ℝ}
    (hT : ‖T‖ ≤ q) (hq : q < 1) : ‖Ring.inverse (1-T)‖ ≤ 1/(1-q) := by
  have hu : IsUnit (1-T) := isUnit_one_sub_of_norm_lt_one (hT.trans_lt hq)
  have hd : 0 < 1-q := sub_pos.mpr hq
  apply opNorm_le_bound _ (by positivity)
  intro f
  let u := Ring.inverse (1-T) f
  have he : u-T u = f := by
    have h := congrArg (fun A : E →L[𝕜] E ↦ A f) (Ring.mul_inverse_cancel _ hu)
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] using h
  have hn : ‖T u‖ ≤ q*‖u‖ :=
    (T.le_opNorm u).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hl : (1-q)*‖u‖ ≤ ‖f‖ := by
    have hh := norm_sub_le (u-T u) (-T u)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg, he] at hh
    nlinarith
  change ‖u‖ ≤ _
  rw [one_div_mul_eq_div, le_div_iff₀ hd]
  simpa only [mul_comm] using hl

/-- Contractive projections preserve small-norm invertibility at every section size. -/
theorem isUnit_liftedFiniteSection_of_norm_lt_one (P T : E →L[𝕜] E)
    (hP : ‖P‖ ≤ 1) (hT : ‖T‖ < 1) : IsUnit (liftedFiniteSection P (-T)) := by
  have hn : ‖P.comp T‖ < 1 := lt_of_le_of_lt
    ((opNorm_comp_le P T).trans (by nlinarith [norm_nonneg T])) hT
  simpa only [liftedFiniteSection, comp_neg, ← sub_eq_add_neg] using
    (isUnit_one_sub_of_norm_lt_one hn)

/-- All contractive sections share the same explicit inverse bound. -/
theorem norm_inverse_liftedFiniteSection_le (P T : E →L[𝕜] E)
    (hP : ‖P‖ ≤ 1) {q : ℝ} (hT : ‖T‖ ≤ q) (hq : q < 1) :
    ‖Ring.inverse (liftedFiniteSection P (-T))‖ ≤ 1/(1-q) := by
  have hn : ‖P.comp T‖ ≤ q :=
    ((opNorm_comp_le P T).trans (by nlinarith [norm_nonneg T])).trans hT
  simpa only [liftedFiniteSection, comp_neg, ← sub_eq_add_neg] using
    norm_inverse_one_sub_le (P.comp T) hn hq

/-- Every section has a projection-tail error bound, without compactness. -/
theorem norm_liftedFiniteSection_error_le_of_norm_lt_one (P T : E →L[𝕜] E)
    (hP : ‖P‖ ≤ 1) {q : ℝ} (hT : ‖T‖ ≤ q) (hq : q < 1) (u : E) :
    ‖Ring.inverse (liftedFiniteSection P (-T)) (P (u-T u)) - u‖ ≤
      (1/(1-q))*‖P u-u‖ := by
  have hu := isUnit_liftedFiniteSection_of_norm_lt_one P T hP (hT.trans_lt hq)
  have he := liftedFiniteSection_error_eq P (-T) hu u
  simp only [add_apply, one_apply_eq_self, neg_apply] at he
  simp only [← sub_eq_add_neg] at he
  rw [he]
  exact (Ring.inverse (liftedFiniteSection P (-T))).le_opNorm _ |>.trans
    (mul_le_mul_of_nonneg_right (norm_inverse_liftedFiniteSection_le P T hP hT hq) (norm_nonneg _))

/-- Strongly convergent contractive sections give convergent small-norm solves. -/
theorem tendsto_liftedFiniteSection_solution_of_norm_lt_one
    (P : ℕ → E →L[𝕜] E) (hP : ∀ n, ‖P n‖ ≤ 1)
    (ht : ∀ u, Tendsto (fun n ↦ P n u) atTop (𝓝 u))
    (T : E →L[𝕜] E) (hT : ‖T‖ < 1) (f : E) :
    Tendsto (fun n ↦ Ring.inverse (liftedFiniteSection (P n) (-T)) (P n f))
      atTop (𝓝 (Ring.inverse (1-T) f)) := by
  let u := Ring.inverse (1-T) f
  have he : u-T u = f := by
    have hh := congrArg (fun A : E →L[𝕜] E ↦ A f)
      (Ring.mul_inverse_cancel (1-T) (isUnit_one_sub_of_norm_lt_one hT))
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] using hh
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb := fun n ↦ norm_liftedFiniteSection_error_le_of_norm_lt_one (P n) T
    (hP n) le_rfl hT u
  rw [he] at hb
  apply squeeze_zero (fun _ ↦ norm_nonneg _) hb
  simpa using ((ht u).sub (tendsto_const_nhds (x := u))).norm.const_mul (1/(1-‖T‖))

omit [CompleteSpace E] in
/-- An inverse-norm bound turns the full residual into an error certificate. -/
theorem norm_sub_inverse_apply_le_residual (B : E →L[𝕜] E) (hB : IsUnit B) (f v : E) :
    ‖v-Ring.inverse B f‖ ≤ ‖Ring.inverse B‖*‖B v-f‖ := by
  have he : Ring.inverse B (B v) = v := by
    have h := congrArg (fun A : E →L[𝕜] E ↦ A v) (Ring.inverse_mul_cancel B hB)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  calc
    _ = ‖Ring.inverse B (B v-f)‖ := by rw [map_sub, he]
    _ ≤ _ := (Ring.inverse B).le_opNorm _

/-- Explicit full-residual error certificate in the small-norm regime. -/
theorem norm_sub_inverse_one_sub_apply_le_residual (T : E →L[𝕜] E)
    {q : ℝ} (hT : ‖T‖ ≤ q) (hq : q < 1) (f v : E) :
    ‖v-Ring.inverse (1-T) f‖ ≤ (1/(1-q))*‖v-T v-f‖ := by
  exact (norm_sub_inverse_apply_le_residual (1-T)
    (isUnit_one_sub_of_norm_lt_one (hT.trans_lt hq)) f v).trans
    (mul_le_mul_of_nonneg_right (norm_inverse_one_sub_le T hT hq) (norm_nonneg _))

end ContinuousLinearMap
