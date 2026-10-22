/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.SingularMass

/-! # Continuous regularizations of power-law kernels

Clamp the distance below by δ and above by 2. On the physical square only
the diagonal is altered. A lower exponent controls the error uniformly in
Schur norm. Reference: weakly singular integral-kernel truncation.
-/

@[expose] public noncomputable section
open Set
namespace Real

/-- A bounded continuous regularization of the distance power on [-1,1]². -/
abbrev PowerLawCutoff (α : ℝ) := {δ : ℝ // 0 < δ ∨ 0 ≤ α}

/-- The entire classical cutoff domain includes zero cutoffs for nonnegative powers. -/
def regularizedPowerLawKernel (α : ℝ) (δ : PowerLawCutoff α) (z : ℝ × ℝ) : ℝ :=
  (max δ.val (min |z.1-z.2| 2)) ^ α

theorem regularizedPowerLawKernel_apply (α : ℝ) (δ : PowerLawCutoff α) (z : ℝ × ℝ) :
    regularizedPowerLawKernel α δ z = (max δ.val (min |z.1-z.2| 2)) ^ α := rfl

theorem regularizedPowerLawKernel_base_domain (α : ℝ) (δ : PowerLawCutoff α) (z : ℝ × ℝ) :
    0 < max δ.val (min |z.1-z.2| 2) ∨
      (0 ≤ max δ.val (min |z.1-z.2| 2) ∧ 0 ≤ α) := by
  rcases δ.property with hd | ha
  · exact Or.inl (hd.trans_le (le_max_left _ _))
  · exact Or.inr ⟨(le_min (abs_nonneg _) (by norm_num)).trans (le_max_right _ _),ha⟩

theorem continuous_regularizedPowerLawKernel_on (α : ℝ) (δ : PowerLawCutoff α) :
    Continuous (regularizedPowerLawKernel α δ) := by
  apply Continuous.rpow_const (by fun_prop)
  intro z
  rcases regularizedPowerLawKernel_base_domain α δ z with h | h
  · exact Or.inl h.ne'
  · exact Or.inr h.2


/-- Positive cutoffs remove the singularity of every real power. -/
theorem continuous_regularizedPowerLawKernel (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (regularizedPowerLawKernel α ⟨δ,Or.inl hδ⟩) := by
  apply Continuous.rpow_const (by fun_prop)
  intro z
  exact Or.inl (ne_of_gt (hδ.trans_le (le_max_left _ _)))

/-- A global bound for the regularized kernel, independent of its coordinates. -/
theorem norm_regularizedPowerLawKernel_le (α : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (z : ℝ × ℝ) :
    ‖regularizedPowerLawKernel α ⟨δ,Or.inl hδ⟩ z‖ ≤ δ^α + (2 : ℝ)^α := by
  rw [regularizedPowerLawKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hα : 0 ≤ α
  · exact (rpow_le_rpow (by positivity) (max_le hδ2 (min_le_right _ _)) hα).trans
      (le_add_of_nonneg_left (by positivity))
  · exact (rpow_le_rpow_of_nonpos hδ (le_max_left _ _) (le_of_not_ge hα)).trans
      (le_add_of_nonneg_right (by positivity))

/-- Away from the diagonal a lower power dominates the regularization error. -/
theorem abs_sub_regularizedPowerLawKernel_le {α β δ : ℝ}
    (hβα : β < α) (hβ : β ≤ 0) (hδ : 0 < δ)
    {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) (hne : x ≠ y) :
    abs (|x-y|^α - regularizedPowerLawKernel α ⟨δ,Or.inl hδ⟩ (x,y)) ≤
      (2 * δ^(α-β)) * |x-y|^β := by
  have ha : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have ha2 : |x-y| ≤ 2 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  simp only [regularizedPowerLawKernel, min_eq_left ha2]
  by_cases hd : δ ≤ |x-y|
  · rw [max_eq_right hd, sub_self, abs_zero]
    positivity
  have had : |x-y| ≤ δ := (lt_of_not_ge hd).le
  rw [max_eq_left had]
  have h1 : |x-y|^α ≤ δ^(α-β)*|x-y|^β := by
    calc
      _ = |x-y|^(α-β)*|x-y|^β := by rw [← rpow_add ha]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (rpow_le_rpow ha.le had (sub_nonneg.mpr hβα.le)) (by positivity)
  have h2 : δ^α ≤ δ^(α-β)*|x-y|^β := by
    calc
      _ = δ^(α-β)*δ^β := by rw [← rpow_add hδ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos ha had hβ) (by positivity)
  calc
    _ ≤ |x-y|^α + δ^α := (abs_sub _ _).trans_eq (by
      rw [abs_of_nonneg (rpow_nonneg (abs_nonneg (x-y)) α),
        abs_of_nonneg (rpow_nonneg hδ.le α)])
    _ ≤ _ := by linarith

/-- In the strict range a slightly lower, negative exponent is still admissible. -/
theorem exists_lower_powerLaw_exponent {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) < α+lam) :
    ∃ β : ℝ, -1 < β ∧ -(1/2) < β+lam ∧ β < α ∧ β < 0 := by
  have h : max (-1 : ℝ) (-lam-1/2) < min α 0 := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    constructor <;> constructor <;> linarith
  obtain ⟨β, hb, hb'⟩ := exists_between h
  exact ⟨β, (max_lt_iff.mp hb).1, by linarith [(max_lt_iff.mp hb).2],
    (lt_min_iff.mp hb').1, (lt_min_iff.mp hb').2⟩

end Real
namespace Real
/-- Physical off-diagonal pairs, on which arbitrary kernel powers exist. -/
abbrev PowerLawOffDiagonalSquare :=
  {z : ℝ × ℝ // z.1 ∈ Icc (-1 : ℝ) 1 ∧ z.2 ∈ Icc (-1 : ℝ) 1 ∧ z.1 ≠ z.2}

theorem norm_regularizedPowerLawKernel_le_on (α : ℝ) (δ : Ioc (0 : ℝ) 2)
    (z : ℝ × ℝ) :
    ‖regularizedPowerLawKernel α ⟨δ.val,Or.inl δ.property.1⟩ z‖ ≤ δ.val^α+(2 : ℝ)^α :=
  norm_regularizedPowerLawKernel_le α δ.property.1 δ.property.2 z

theorem abs_sub_regularizedPowerLawKernel_le_on {α β : ℝ}
    (hβα : β < α) (hβ : β ≤ 0) (δ : Ioi (0 : ℝ)) (z : PowerLawOffDiagonalSquare) :
    abs (|z.val.1-z.val.2|^α - regularizedPowerLawKernel α ⟨δ.val,Or.inl δ.property⟩ z.val) ≤
      (2*δ.val^(α-β))*|z.val.1-z.val.2|^β :=
  abs_sub_regularizedPowerLawKernel_le hβα hβ δ.property
    z.property.1 z.property.2.1 z.property.2.2
end Real
