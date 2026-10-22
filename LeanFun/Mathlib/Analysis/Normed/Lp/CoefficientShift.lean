/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Lp.CoefficientOperators
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Unilateral shifts of square-summable coefficients
These bounded shifts implement the banded scalar recurrences used by spectral
operators. Reference: Olver--Townsend (2013), Section 4.
-/

@[expose] public section
namespace lp
open Filter
open scoped Topology ENNReal

private theorem two_pos : 0 < (2 : ℝ≥0∞).toReal := by norm_num

/-- Removing the first coordinate is a contraction. -/
noncomputable def coefficientShiftLeft :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟨fun i ↦ x (i + 1),
        (memℓp_gen_iff two_pos).2
          ((summable_nat_add_iff 1).2 ((lp.memℓp x).summable two_pos))⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun x ↦ by
      rw [one_mul]
      apply lp.norm_le_of_tsum_le two_pos (norm_nonneg x)
      rw [lp.norm_rpow_eq_tsum two_pos]
      exact Summable.tsum_le_tsum_of_inj (fun i ↦ i + 1) (add_left_injective 1)
        (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl)
        ((summable_nat_add_iff 1).2 ((lp.memℓp x).summable two_pos))
        ((lp.memℓp x).summable two_pos))

@[simp] theorem coefficientShiftLeft_apply (x : lp (fun _ : ℕ ↦ ℂ) 2) (i : ℕ) :
    coefficientShiftLeft x i = x (i + 1) := rfl

/-- Inserting a zero first coordinate is an isometric shift. -/
noncomputable def coefficientShiftRight :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟨fun i ↦ if i = 0 then 0 else x (i - 1),
        (memℓp_gen_iff two_pos).2 ((summable_nat_add_iff 1).1
          (by simpa using (lp.memℓp x).summable two_pos))⟩
      map_add' := fun x y ↦ by
        apply lp.ext
        funext i
        change (if i = 0 then 0 else x (i - 1) + y (i - 1)) =
          (if i = 0 then 0 else x (i - 1)) + (if i = 0 then 0 else y (i - 1))
        split_ifs <;> simp
      map_smul' := fun a x ↦ by
        apply lp.ext
        funext i
        change (if i = 0 then 0 else a * x (i - 1)) = a * (if i = 0 then 0 else x (i - 1))
        split_ifs <;> simp }
    1 (fun x ↦ by
      rw [one_mul]
      apply lp.norm_le_of_tsum_le two_pos (norm_nonneg x)
      rw [lp.norm_rpow_eq_tsum two_pos]
      have hs : Summable (fun i ↦ ‖(if i = 0 then (0 : ℂ) else x (i - 1))‖ ^ (2 : ℝ≥0∞).toReal) :=
        (summable_nat_add_iff 1).1 (by simpa using (lp.memℓp x).summable two_pos)
      change (∑' i : ℕ, ‖(if i = 0 then (0 : ℂ) else x (i - 1))‖ ^ (2 : ℝ≥0∞).toReal) ≤ _
      rw [hs.tsum_eq_zero_add]
      simp)

@[simp] theorem coefficientShiftRight_zero (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    coefficientShiftRight x 0 = 0 := by rfl

@[simp] theorem coefficientShiftRight_succ (x : lp (fun _ : ℕ ↦ ℂ) 2) (i : ℕ) :
    coefficientShiftRight x (i + 1) = x i := by
  change (if i + 1 = 0 then 0 else x (i + 1 - 1)) = x i
  simp

/-- Left shift cancels a preceding right shift. -/
theorem coefficientShiftLeft_comp_right :
    coefficientShiftLeft.comp coefficientShiftRight = 1 := by
  ext x i
  simp [one_apply_eq_self]

/-- The opposite composition removes the first coordinate. -/
theorem coefficientShiftRight_comp_left :
    coefficientShiftRight.comp coefficientShiftLeft = 1 - coefficientProjection 1 := by
  ext x i
  cases i <;> simp [one_apply_eq_self]

end lp
