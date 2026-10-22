/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Complex.Basic
public import LeanFun.Mathlib.Analysis.Analytic.OpenDomain
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Joukowski map and Bernstein ellipses

The open filled ellipse is described by the sum of distances to its foci `±1`.
The image descriptions connect this geometric definition to complex analysis.

Reference: Trefethen, *Approximation Theory and Approximation Practice*, Chapter 8.
-/

public section

namespace Complex

/-- The Joukowski map, used away from zero (ATAP, Chapter 8). -/
@[expose] noncomputable def joukowski (z : {z : ℂ // z ≠ 0}) : ℂ := (z.val + z.val⁻¹) / 2

/-- The open filled Bernstein ellipse, with parameter `ρ > 1` (ATAP, Chapter 8). -/
def bernsteinEllipse (ρ : Set.Ioi (1 : ℝ)) : Set ℂ :=
  {w | ‖w - 1‖ + ‖w + 1‖ < (ρ : ℝ) + (ρ : ℝ)⁻¹}

/-- Membership in the classical ellipse (ATAP, Chapter 8). -/
theorem mem_bernsteinEllipse_iff (ρ : Set.Ioi (1 : ℝ)) (w : ℂ) :
    w ∈ bernsteinEllipse ρ ↔ ‖w - 1‖ + ‖w + 1‖ < (ρ : ℝ) + (ρ : ℝ)⁻¹ := Iff.rfl

/-- Classical value of the Joukowski map (ATAP, Chapter 8). -/
theorem joukowski_apply (z : {z : ℂ // z ≠ 0}) :
    joukowski z = (z.val + z.val⁻¹) / 2 := rfl

/-- Inversion leaves the Joukowski map unchanged (ATAP, Chapter 8). -/
@[simp] theorem joukowski_inv (z : {z : ℂ // z ≠ 0}) :
    joukowski ⟨z.val⁻¹, inv_ne_zero z.property⟩ = joukowski z := by
  simp [joukowski, add_comm]

/-- The Joukowski map respects negation (ATAP, Chapter 8). -/
@[simp] theorem joukowski_neg (z : {z : ℂ // z ≠ 0}) :
    joukowski ⟨-z.val, neg_ne_zero.mpr z.property⟩ = -joukowski z := by
  simp [joukowski]; ring

/-- Factoring the distance to the right focus (ATAP, Chapter 8). -/
theorem joukowski_sub_one (z : {z : ℂ // z ≠ 0}) :
    joukowski z - 1 = (z.val - 1) ^ 2 / (2 * z.val) := by
  unfold joukowski
  field_simp [z.property]
  ring

/-- Factoring the distance to the left focus (ATAP, Chapter 8). -/
theorem joukowski_add_one (z : {z : ℂ // z ≠ 0}) :
    joukowski z + 1 = (z.val + 1) ^ 2 / (2 * z.val) := by
  unfold joukowski
  field_simp [z.property]
  ring

/-- The focal-distance identity underlying Bernstein ellipses (ATAP, Chapter 8). -/
theorem norm_joukowski_sub_one_add_norm_joukowski_add_one (z : {z : ℂ // z ≠ 0}) :
    ‖joukowski z - 1‖ + ‖joukowski z + 1‖ = ‖z.val‖ + ‖z.val‖⁻¹ := by
  rw [joukowski_sub_one z, joukowski_add_one z]
  simp only [norm_div, norm_pow, norm_mul, norm_ofNat]
  have h : ‖z.val - 1‖ ^ 2 + ‖z.val + 1‖ ^ 2 = 2 * (‖z.val‖ ^ 2 + 1) := by
    simp only [← normSq_eq_norm_sq, normSq_apply, sub_re, sub_im, add_re, add_im,
      one_re, one_im]
    ring
  rw [← add_div, h]
  field_simp

/-- The filled Bernstein ellipse is open (ATAP, Chapter 8). -/
theorem isOpen_bernsteinEllipse (ρ : Set.Ioi (1 : ℝ)) : IsOpen (bernsteinEllipse ρ) := by
  apply isOpen_lt _ continuous_const
  fun_prop

/-- Every complex point has a nonzero Joukowski preimage (ATAP, Chapter 8). -/
theorem exists_joukowski_eq (w : ℂ) : ∃ z : {z : ℂ // z ≠ 0}, joukowski z = w := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w ^ 2 - 1) (by decide : 0 < 2)
  have hprod : (w + s) * (w - s) = 1 := by linear_combination -hs
  have hz : w + s ≠ 0 := by intro h; simp [h] at hprod
  refine ⟨⟨w + s, hz⟩, ?_⟩
  have hinv : (w + s)⁻¹ = w - s := by
    exact inv_eq_of_mul_eq_one_right hprod
  change (w + s + (w + s)⁻¹) / 2 = w
  rw [hinv]
  ring

private theorem radius_inequality {r ρ : ℝ} (hr : 0 < r) (hρ : 1 < ρ) :
    r + r⁻¹ < ρ + ρ⁻¹ ↔ ρ⁻¹ < r ∧ r < ρ := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hi : ρ⁻¹ < 1 := (inv_lt_one₀ hρ0).2 hρ
  have heq : (r + r⁻¹ - (ρ + ρ⁻¹)) * (r * ρ) = (r - ρ) * (r * ρ - 1) := by
    field_simp
    ring
  have hsign : r + r⁻¹ < ρ + ρ⁻¹ ↔ (r - ρ) * (r * ρ - 1) < 0 := by
    rw [← heq, mul_neg_iff]
    have hp := mul_pos hr hρ0
    constructor
    · intro h; exact Or.inr ⟨sub_neg.mpr h, hp⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · linarith
      · exact sub_neg.mp h
  rw [hsign, mul_neg_iff]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · have : ρ * ρ < r * ρ := mul_lt_mul_of_pos_right (by linarith) hρ0
      nlinarith
    · exact ⟨(inv_lt_iff_one_lt_mul₀ hρ0).2 (by nlinarith), by linarith⟩
  · rintro ⟨h, h'⟩
    exact Or.inr ⟨sub_neg.mpr h', sub_pos.mpr ((inv_lt_iff_one_lt_mul₀ hρ0).1 h)⟩

/-- The preimage of the open ellipse is precisely the open annulus (ATAP, Chapter 8). -/
theorem joukowski_mem_bernsteinEllipse_iff {ρ : ℝ} (hρ : 1 < ρ)
    (z : {z : ℂ // z ≠ 0}) :
    joukowski z ∈ bernsteinEllipse ⟨ρ, hρ⟩ ↔ ρ⁻¹ < ‖z.val‖ ∧ ‖z.val‖ < ρ := by
  change ‖joukowski z - 1‖ + ‖joukowski z + 1‖ < ρ + ρ⁻¹ ↔ _
  rw [norm_joukowski_sub_one_add_norm_joukowski_add_one z]
  exact radius_inequality (norm_pos_iff.mpr z.property) hρ

/-- The open Bernstein ellipse is the Joukowski image of an annulus (ATAP, Chapter 8). -/
theorem bernsteinEllipse_eq_image_annulus {ρ : ℝ} (hρ : 1 < ρ) :
    bernsteinEllipse ⟨ρ, hρ⟩ = joukowski ''
      {z : {z : ℂ // z ≠ 0} | ρ⁻¹ < ‖z.val‖ ∧ ‖z.val‖ < ρ} := by
  ext w
  constructor
  · intro hw
    obtain ⟨z, rfl⟩ := exists_joukowski_eq w
    exact ⟨z, (joukowski_mem_bernsteinEllipse_iff hρ z).1 hw, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact (joukowski_mem_bernsteinEllipse_iff hρ z).2 hz

/-- The whole approximation interval lies inside the open ellipse (ATAP, Chapter 8). -/
theorem ofReal_mem_bernsteinEllipse {ρ x : ℝ} (hρ : 1 < ρ) (hx : x ∈ Set.Icc (-1) 1) :
    (x : ℂ) ∈ bernsteinEllipse ⟨ρ, hρ⟩ := by
  have hρ0 : 0 < ρ := by linarith
  have h2 : 2 < ρ + ρ⁻¹ := by
    have h := (radius_inequality (by norm_num : (0 : ℝ) < 1) hρ).2
      ⟨(inv_lt_one₀ hρ0).2 hρ, hρ⟩
    norm_num at h ⊢
    exact h
  change ‖(x : ℂ) - 1‖ + ‖(x : ℂ) + 1‖ < _
  rw [← ofReal_one, ← ofReal_sub, ← ofReal_add, norm_real, norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.2]),
    abs_of_nonneg (by linarith [hx.1])]
  linarith

/-- The Joukowski map is analytic on its punctured-plane domain (ATAP, Chapter 8). -/
theorem analyticOnOpen_joukowski :
    AnalyticOnOpen ⟨{z : ℂ | z ≠ 0}, isOpen_ne⟩ joukowski := by
  intro z
  refine ⟨fun w => (w + w⁻¹) / 2, fun _ => rfl, ?_⟩
  exact (analyticAt_id.add (analyticAt_id.inv z.property)).div analyticAt_const (by norm_num)

/-- Internal local-expression bridge; the centre is nonzero. -/
theorem analyticAt_joukowski_expression {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => (w + w⁻¹) / 2) z :=
  ((analyticOnOpen_iff ⟨{w : ℂ | w ≠ 0}, isOpen_ne⟩ joukowski
    (fun w => (w + w⁻¹) / 2) (fun _ => rfl)).1 analyticOnOpen_joukowski) z hz

/-- Continuity on the actual nonzero domain (ATAP, Chapter 8). -/
theorem continuous_joukowski : Continuous joukowski :=
  (continuous_subtype_val.add (continuous_subtype_val.inv₀ (fun z => z.property))).div_const 2

/-- A circle of radius `ρ` maps to the focal-distance level set (ATAP, Chapter 8). -/
theorem image_joukowski_sphere {ρ : ℝ} (hρ : 1 < ρ) :
    joukowski '' {z : {z : ℂ // z ≠ 0} | ‖z.val‖ = ρ} =
      {w : ℂ | ‖w - 1‖ + ‖w + 1‖ = ρ + ρ⁻¹} := by
  have hρ0 : 0 < ρ := by linarith
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ‖joukowski z - 1‖ + ‖joukowski z + 1‖ = _
    rw [norm_joukowski_sub_one_add_norm_joukowski_add_one z, hz]
  · intro hw
    obtain ⟨z, rfl⟩ := exists_joukowski_eq w
    change ‖joukowski z - 1‖ + ‖joukowski z + 1‖ = _ at hw
    rw [norm_joukowski_sub_one_add_norm_joukowski_add_one z] at hw
    have hn : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
    have heq : (‖z.val‖ - ρ) * (‖z.val‖ * ρ - 1) = 0 := by
      have hm := congrArg (fun t : ℝ => t * (‖z.val‖ * ρ)) hw
      field_simp at hm
      nlinarith [hm]
    rcases mul_eq_zero.mp heq with h | h
    · exact ⟨z, sub_eq_zero.mp h, rfl⟩
    · refine ⟨⟨z.val⁻¹, inv_ne_zero z.property⟩, ?_, joukowski_inv z⟩
      change ‖z.val⁻¹‖ = ρ
      rw [norm_inv]
      apply (inv_eq_iff_eq_inv).2
      rw [inv_eq_one_div]
      apply (eq_div_iff (ne_of_gt hρ0)).2
      simpa using sub_eq_zero.mp h

/-- Each circle-image point is approached from inside the ellipse (ATAP, Chapter 8). -/
theorem joukowski_mem_closure_bernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ)
    (z : {z : ℂ // z ≠ 0}) (hz : ‖z.val‖ = ρ) :
    joukowski z ∈ closure (bernsteinEllipse ⟨ρ, hρ⟩) := by
  have hρ0 : 0 < ρ := by linarith
  let g : ℝ → ℂ := fun t => (t : ℂ) / (ρ : ℂ) * z.val
  have hg : g ρ = z.val := by simp [g, ne_of_gt hρ0]
  have hc : ContinuousAt (fun t => (g t + (g t)⁻¹) / 2) ρ := by
    apply (analyticAt_joukowski_expression z.property).continuousAt.comp_of_eq
      (by fun_prop : ContinuousAt g ρ) hg
  have ht : ρ ∈ closure (Set.Ioo (1 : ℝ) ρ) := by
    rw [closure_Ioo (ne_of_lt hρ)]
    exact ⟨le_of_lt hρ, le_rfl⟩
  have hmem := mem_closure_image hc ht
  simp only [hg] at hmem
  change joukowski z ∈ closure ((fun t => (g t + (g t)⁻¹) / 2) '' Set.Ioo 1 ρ) at hmem
  apply closure_mono (s := (fun t => (g t + (g t)⁻¹) / 2) '' Set.Ioo 1 ρ) _ hmem
  rintro _ ⟨t, ht, rfl⟩
  have ht0 : 0 < t := by linarith [ht.1]
  have hnorm : ‖g t‖ = t := by
    simp [g, norm_real, Real.norm_eq_abs, abs_of_pos ht0,
      abs_of_pos hρ0, hz, ne_of_gt hρ0]
  have hg0 : g t ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; exact ht0)
  change joukowski ⟨g t, hg0⟩ ∈ _
  apply (joukowski_mem_bernsteinEllipse_iff hρ ⟨g t, hg0⟩).2
  change ρ⁻¹ < ‖g t‖ ∧ ‖g t‖ < ρ
  rw [hnorm]
  exact ⟨lt_trans ((inv_lt_one₀ hρ0).2 hρ) ht.1, ht.2⟩

/-- The boundary of the open filled ellipse is exactly the circle image (ATAP, Chapter 8). -/
theorem frontier_bernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ) :
    frontier (bernsteinEllipse ⟨ρ, hρ⟩) = joukowski '' {z : {z : ℂ // z ≠ 0} | ‖z.val‖ = ρ} := by
  apply Set.Subset.antisymm
  · rw [image_joukowski_sphere hρ]
    exact frontier_lt_subset_eq (by fun_prop) continuous_const
  · rintro w ⟨z, hz, rfl⟩
    have hn : ‖z.val‖ = ρ := hz
    rw [(isOpen_bernsteinEllipse ⟨ρ, hρ⟩).frontier_eq]
    refine ⟨joukowski_mem_closure_bernsteinEllipse hρ z hn, ?_⟩
    have heq : joukowski z ∈ {w : ℂ | ‖w - 1‖ + ‖w + 1‖ = ρ + ρ⁻¹} :=
      (image_joukowski_sphere hρ).subset ⟨z, hz, rfl⟩
    change ¬ ‖joukowski z - 1‖ + ‖joukowski z + 1‖ < ρ + ρ⁻¹
    exact not_lt.mpr (le_of_eq heq.symm)


/-- Every point of an open ellipse belongs to a strictly smaller ellipse
(ATAP, Chapter 8, local convergence argument). -/
theorem exists_smaller_bernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ) {z : ℂ}
    (hz : z ∈ bernsteinEllipse ⟨ρ, hρ⟩) : ∃ r, ∃ hr : 1 < r, r < ρ ∧ z ∈ bernsteinEllipse ⟨r, hr⟩ := by
  rw [bernsteinEllipse_eq_image_annulus hρ] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hρ0 : 0 < ρ := by linarith
  have hw0 : 0 < ‖w.val‖ := lt_trans (inv_pos.mpr hρ0) hw.1
  have hi : ‖w.val‖⁻¹ < ρ := (inv_lt_comm₀ hw0 hρ0).2 hw.1
  obtain ⟨r, hr, hrρ⟩ := exists_between (max_lt hρ (max_lt hw.2 hi))
  have hr1 : 1 < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hwr : ‖w.val‖ < r := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hr
  have hir : ‖w.val‖⁻¹ < r := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hr
  refine ⟨r, hr1, hrρ, (joukowski_mem_bernsteinEllipse_iff hr1 w).2 ?_⟩
  exact ⟨(inv_lt_comm₀ (by linarith : 0 < r) hw0).2 hir, hwr⟩

/-- The closure of a smaller Bernstein ellipse lies inside a larger open one. -/
theorem closure_bernsteinEllipse_subset {r ρ : ℝ} (hr : 1 < r) (hrρ : r < ρ) :
    closure (bernsteinEllipse ⟨r, hr⟩) ⊆ bernsteinEllipse ⟨ρ, hr.trans hrρ⟩ := by
  have hr0 : 0 < r := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hlevel : r + r⁻¹ < ρ + ρ⁻¹ := by
    have heq : (ρ + ρ⁻¹ - (r + r⁻¹)) * (r * ρ) = (ρ - r) * (r * ρ - 1) := by
      field_simp
      ring
    have hp : 0 < (ρ - r) * (r * ρ - 1) := mul_pos (sub_pos.mpr hrρ) (by nlinarith)
    have hmul : 0 < r * ρ := mul_pos hr0 hρ0
    nlinarith
  have hcl : closure (bernsteinEllipse ⟨r, hr⟩) ⊆ {z : ℂ | ‖z - 1‖ + ‖z + 1‖ ≤ r + r⁻¹} :=
    closure_minimal (by
      intro z hz
      change ‖z - 1‖ + ‖z + 1‖ ≤ r + r⁻¹
      exact le_of_lt hz) (isClosed_le (by fun_prop) continuous_const)
  exact fun z hz ↦ (hcl hz).trans_lt hlevel

/-- Closed smaller ellipses are compact (ATAP, Chapter 8). -/
theorem isCompact_closure_bernsteinEllipse (r : Set.Ioi (1 : ℝ)) :
    IsCompact (closure (bernsteinEllipse r)) := by
  apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
  apply Bornology.IsBounded.closure
  apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (r : ℝ) + (r : ℝ)⁻¹ + 1)).subset
  intro z hz
  have hn : ‖z‖ ≤ ‖z - 1‖ + 1 := by
    simpa using norm_add_le (z - 1) (1 : ℂ)
  simp only [Metric.mem_closedBall, dist_zero_right]
  change ‖z - 1‖ + ‖z + 1‖ < (r : ℝ) + (r : ℝ)⁻¹ at hz
  linarith [norm_nonneg (z + 1)]

end Complex
