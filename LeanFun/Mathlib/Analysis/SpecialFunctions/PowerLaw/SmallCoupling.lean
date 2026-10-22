/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Solve
public import LeanFun.Mathlib.Analysis.Normed.Operator.SmallNormSolve

/-! # Power-law solves on the full boundedness range

Small coupling gives stable finite solves even on the noncompact critical line.
The error certificates use the full residual, including unresolved coordinates.
Reference: the Neumann-series perturbation argument applied to the weighted
power-law operator of Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

public noncomputable section
open MeasureTheory Polynomial Filter ContinuousLinearMap
open scoped Topology Matrix
namespace Real
variable {α lam c : ℝ} (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam)

private theorem norm_smul_powerLawCoefficientOperator :
    ‖c • boundedPowerLawCoefficientOperator hα hlam hs‖ =
      |c| * ‖boundedPowerLawL2Operator hα hlam hs‖ := by
  rw [norm_smul, Real.norm_eq_abs, norm_boundedPowerLawCoefficientOperator]

/-- A physical residual gives an error certificate whenever the equation is invertible. -/
theorem norm_powerLawL2_error_le_residual
    (hT : IsUnit (1-c • boundedPowerLawL2Operator hα hlam hs))
    (f v : Lp ℝ 2 (gegenbauerMeasure lam)) :
    ‖v-Ring.inverse (1-c • boundedPowerLawL2Operator hα hlam hs) f‖ ≤
      ‖Ring.inverse (1-c • boundedPowerLawL2Operator hα hlam hs)‖ *
        ‖v-c • boundedPowerLawL2Operator hα hlam hs v-f‖ :=
  norm_sub_inverse_apply_le_residual _ hT f v

/-- The full coefficient residual controls error under the general invertibility hypothesis. -/
theorem norm_powerLawCoefficient_error_le_residual
    (hT : IsUnit (1-c • boundedPowerLawCoefficientOperator hα hlam hs))
    (f v : lp (fun _ : ℕ ↦ ℝ) 2) :
    ‖v-Ring.inverse (1-c • boundedPowerLawCoefficientOperator hα hlam hs) f‖ ≤
      ‖Ring.inverse (1-c • boundedPowerLawCoefficientOperator hα hlam hs)‖ *
        ‖v-c • boundedPowerLawCoefficientOperator hα hlam hs v-f‖ :=
  norm_sub_inverse_apply_le_residual _ hT f v

variable (hc : |c| * ‖boundedPowerLawL2Operator hα hlam hs‖ < 1)
include hc

/-- At small coupling every normalized section is invertible, including on the critical line. -/
theorem isUnit_powerLaw_section_of_small_coupling (N : ℕ) :
    IsUnit (1-(lp.initialL2Projection (𝕜 := ℝ) N).comp (c • boundedPowerLawCoefficientOperator hα hlam hs)) := by
  simpa only [liftedFiniteSection, comp_neg, ← sub_eq_add_neg] using
    isUnit_liftedFiniteSection_of_norm_lt_one (lp.initialL2Projection (𝕜 := ℝ) N)
      (c • boundedPowerLawCoefficientOperator hα hlam hs) (lp.norm_initialL2Projection_le (𝕜 := ℝ) N)
      (by rwa [norm_smul_powerLawCoefficientOperator])

/-- An explicit inverse bound holds uniformly for all section sizes. -/
theorem norm_inverse_powerLaw_section_le_of_small_coupling (N : ℕ) :
    ‖Ring.inverse (1-(lp.initialL2Projection (𝕜 := ℝ) N).comp
      (c • boundedPowerLawCoefficientOperator hα hlam hs))‖ ≤
        1/(1-|c| * ‖boundedPowerLawL2Operator hα hlam hs‖) := by
  simpa only [liftedFiniteSection, comp_neg, ← sub_eq_add_neg] using
    norm_inverse_liftedFiniteSection_le (lp.initialL2Projection (𝕜 := ℝ) N)
      (c • boundedPowerLawCoefficientOperator hα hlam hs) (lp.norm_initialL2Projection_le (𝕜 := ℝ) N)
      (norm_smul_powerLawCoefficientOperator hα hlam hs).le hc

/-- Every projected equation has a unique solution, without a compactness hypothesis. -/
theorem existsUnique_powerLaw_projected_solution_of_small_coupling (N : ℕ)
    (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    ∃! u, lp.initialL2Projection N u = u ∧
      lp.initialL2Projection N (u-c • boundedPowerLawCoefficientOperator hα hlam hs u) =
        lp.initialL2Projection N f := by
  simpa only [add_apply, one_apply_eq_self, _root_.neg_apply, smul_apply, sub_eq_add_neg] using
    existsUnique_projected_solution (lp.initialL2Projection (𝕜 := ℝ) N)
      (-(c • boundedPowerLawCoefficientOperator hα hlam hs))
      (lp.initialL2Projection_idempotent N)
      (by simpa only [liftedFiniteSection, comp_neg, ← sub_eq_add_neg] using
        isUnit_powerLaw_section_of_small_coupling hα hlam hs hc N) f

/-- Every actual finite normalized matrix has a unique solution at small coupling. -/
theorem existsUnique_powerLaw_matrix_solution_of_small_coupling (N : ℕ)
    (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    ∃! v : Fin N → ℝ,
      (1-lp.initialL2Matrix (c • boundedPowerLawCoefficientOperator hα hlam hs) N) *ᵥ v =
        (fun i : Fin N ↦ f i) :=
  lp.existsUnique_initialL2Matrix_solution _ N f
    (existsUnique_powerLaw_projected_solution_of_small_coupling hα hlam hs hc N f)

/-- The projection-tail error estimate holds at every resolution throughout the bounded range. -/
theorem norm_powerLaw_section_error_le_of_small_coupling (N : ℕ)
    (u : lp (fun _ : ℕ ↦ ℝ) 2) :
    ‖Ring.inverse (1-(lp.initialL2Projection (𝕜 := ℝ) N).comp (c • boundedPowerLawCoefficientOperator hα hlam hs))
      (lp.initialL2Projection N (u-c • boundedPowerLawCoefficientOperator hα hlam hs u))-u‖ ≤
        (1/(1-|c| * ‖boundedPowerLawL2Operator hα hlam hs‖))*‖lp.initialL2Projection N u-u‖ := by
  simpa only [liftedFiniteSection, comp_neg, ← sub_eq_add_neg, smul_apply] using
    norm_liftedFiniteSection_error_le_of_norm_lt_one (lp.initialL2Projection (𝕜 := ℝ) N)
      (c • boundedPowerLawCoefficientOperator hα hlam hs) (lp.norm_initialL2Projection_le (𝕜 := ℝ) N)
      (norm_smul_powerLawCoefficientOperator hα hlam hs).le hc u

/-- Normalized finite solves converge even on the noncompact critical line at small coupling. -/
theorem tendsto_powerLaw_section_solution_of_small_coupling (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N ↦ Ring.inverse
      (1-(lp.initialL2Projection (𝕜 := ℝ) N).comp (c • boundedPowerLawCoefficientOperator hα hlam hs))
        (lp.initialL2Projection N f)) atTop
      (𝓝 (Ring.inverse (1-c • boundedPowerLawCoefficientOperator hα hlam hs) f)) := by
  simpa only [liftedFiniteSection, comp_neg, ← sub_eq_add_neg] using
    tendsto_liftedFiniteSection_solution_of_norm_lt_one _ lp.norm_initialL2Projection_le
      lp.tendsto_initialL2Projection (c • boundedPowerLawCoefficientOperator hα hlam hs)
      (by rwa [norm_smul_powerLawCoefficientOperator]) f

/-- An explicit physical error certificate uses the complete second-kind residual. -/
theorem norm_powerLawL2_error_le_residual_of_small_coupling
    (f v : Lp ℝ 2 (gegenbauerMeasure lam)) :
    ‖v-Ring.inverse (1-c • boundedPowerLawL2Operator hα hlam hs) f‖ ≤
      (1/(1-|c| * ‖boundedPowerLawL2Operator hα hlam hs‖)) *
        ‖v-c • boundedPowerLawL2Operator hα hlam hs v-f‖ := by
  apply norm_sub_inverse_one_sub_apply_le_residual _ _ hc
  rw [norm_smul, Real.norm_eq_abs]

/-- An explicit coefficient error certificate includes all unresolved residual coordinates. -/
theorem norm_powerLawCoefficient_error_le_residual_of_small_coupling
    (f v : lp (fun _ : ℕ ↦ ℝ) 2) :
    ‖v-Ring.inverse (1-c • boundedPowerLawCoefficientOperator hα hlam hs) f‖ ≤
      (1/(1-|c| * ‖boundedPowerLawL2Operator hα hlam hs‖)) *
        ‖v-c • boundedPowerLawCoefficientOperator hα hlam hs v-f‖ :=
  norm_sub_inverse_one_sub_apply_le_residual _
    (norm_smul_powerLawCoefficientOperator hα hlam hs).le hc f v

end Real

namespace Real
variable {α lam c : ℝ} (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam)
private theorem inverse_eq_certified {M : Type*} [MonoidWithZero M] {x : M} (h : IsUnit x) :
    Ring.inverse x = ↑(h.unit⁻¹) := by
  simpa only [IsUnit.unit_spec] using Ring.inverse_unit h.unit

theorem norm_powerLawL2_error_le_residualOn (hT : IsUnit (1-c • boundedPowerLawL2Operator hα hlam hs)) (f v : Lp ℝ 2 (gegenbauerMeasure lam)) : ‖v-(↑((hT).unit⁻¹) : Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam)) f‖ ≤ ‖(↑((hT).unit⁻¹) : Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam))‖ * ‖v-c • boundedPowerLawL2Operator hα hlam hs v-f‖:= by
  simpa only [inverse_eq_certified (hT)] using norm_powerLawL2_error_le_residual hα hlam hs hT f v

theorem norm_powerLawCoefficient_error_le_residualOn (hT : IsUnit (1-c • boundedPowerLawCoefficientOperator hα hlam hs)) (f v : lp (fun _ : ℕ ↦ ℝ) 2) : ‖v-(↑((hT).unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2) f‖ ≤ ‖(↑((hT).unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2)‖ * ‖v-c • boundedPowerLawCoefficientOperator hα hlam hs v-f‖:= by
  simpa only [inverse_eq_certified (hT)] using norm_powerLawCoefficient_error_le_residual hα hlam hs hT f v

variable (hc : |c| * ‖boundedPowerLawL2Operator hα hlam hs‖ < 1)

theorem norm_inverse_powerLaw_section_le_of_small_couplingOn (N : ℕ) : ‖(↑((isUnit_powerLaw_section_of_small_coupling hα hlam hs hc N).unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2)‖ ≤ 1/(1-|c| * ‖boundedPowerLawL2Operator hα hlam hs‖):= by
  simpa only [inverse_eq_certified (isUnit_powerLaw_section_of_small_coupling hα hlam hs hc N)] using norm_inverse_powerLaw_section_le_of_small_coupling hα hlam hs hc N

theorem norm_powerLaw_section_error_le_of_small_couplingOn (N : ℕ) (u : lp (fun _ : ℕ ↦ ℝ) 2) : ‖(↑((isUnit_powerLaw_section_of_small_coupling hα hlam hs hc N).unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2) (lp.initialL2Projection N (u-c • boundedPowerLawCoefficientOperator hα hlam hs u))-u‖ ≤ (1/(1-|c| * ‖boundedPowerLawL2Operator hα hlam hs‖))*‖lp.initialL2Projection N u-u‖:= by
  simpa only [inverse_eq_certified (isUnit_powerLaw_section_of_small_coupling hα hlam hs hc N)] using norm_powerLaw_section_error_le_of_small_coupling hα hlam hs hc N u

theorem tendsto_powerLaw_section_solution_of_small_couplingOn (f : lp (fun _ : ℕ ↦ ℝ) 2) : Tendsto (fun N ↦ (↑((isUnit_powerLaw_section_of_small_coupling hα hlam hs hc N).unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2) (lp.initialL2Projection N f)) atTop (𝓝 ((↑((isUnit_one_sub_smul_powerLawCoefficientOperator_of_norm_lt_one hα hlam hs hc).unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2) f)):= by
  simpa only [inverse_eq_certified (isUnit_one_sub_smul_powerLawCoefficientOperator_of_norm_lt_one hα hlam hs hc), inverse_eq_certified (isUnit_powerLaw_section_of_small_coupling hα hlam hs hc _)] using tendsto_powerLaw_section_solution_of_small_coupling hα hlam hs hc f

theorem norm_powerLawL2_error_le_residual_of_small_couplingOn (f v : Lp ℝ 2 (gegenbauerMeasure lam)) : ‖v-(↑(((isUnit_one_sub_smul_powerLawCoefficientOperator_iff hα hlam hs).mp (isUnit_one_sub_smul_powerLawCoefficientOperator_of_norm_lt_one hα hlam hs hc)).unit⁻¹) : Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam)) f‖ ≤ (1/(1-|c| * ‖boundedPowerLawL2Operator hα hlam hs‖)) * ‖v-c • boundedPowerLawL2Operator hα hlam hs v-f‖:= by
  simpa only [inverse_eq_certified ((isUnit_one_sub_smul_powerLawCoefficientOperator_iff hα hlam hs).mp (isUnit_one_sub_smul_powerLawCoefficientOperator_of_norm_lt_one hα hlam hs hc))] using norm_powerLawL2_error_le_residual_of_small_coupling hα hlam hs hc f v

theorem norm_powerLawCoefficient_error_le_residual_of_small_couplingOn (f v : lp (fun _ : ℕ ↦ ℝ) 2) : ‖v-(↑((isUnit_one_sub_smul_powerLawCoefficientOperator_of_norm_lt_one hα hlam hs hc).unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2) f‖ ≤ (1/(1-|c| * ‖boundedPowerLawL2Operator hα hlam hs‖)) * ‖v-c • boundedPowerLawCoefficientOperator hα hlam hs v-f‖:= by
  simpa only [inverse_eq_certified (isUnit_one_sub_smul_powerLawCoefficientOperator_of_norm_lt_one hα hlam hs hc)] using norm_powerLawCoefficient_error_le_residual_of_small_coupling hα hlam hs hc f v
end Real
