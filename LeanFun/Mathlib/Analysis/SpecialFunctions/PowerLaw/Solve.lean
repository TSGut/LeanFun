/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Compact
public import LeanFun.Mathlib.Analysis.InnerProductSpace.FiniteMatrix
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Stable second-kind power-law solves

Compactness gives stable finite sections whenever the limiting second-kind
operator is invertible. Small coupling is an explicit sufficient condition,
not a restriction on the general theorem. Optimisation is outside this scope.
Reference: compact finite-section stability, Olver–Townsend (2013), §4.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter ContinuousLinearMap
open scoped Topology Matrix
namespace Real

/-- The physical and normalized coefficient second-kind equations have exactly
the same invertibility condition. -/
theorem isUnit_one_sub_smul_powerLawCoefficientOperator_iff
    {α lam c : ℝ} (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam) :
    IsUnit (1 - c • boundedPowerLawCoefficientOperator hα hlam hs) ↔
      IsUnit (1 - c • boundedPowerLawL2Operator hα hlam hs) := by
  let e := (powerLawHilbertBasis hlam).repr.toContinuousLinearEquiv.conjContinuousAlgEquiv
  have h := MulEquiv.isUnit_map (f := e.toAlgEquiv.toMulEquiv)
    (x := 1 - c • boundedPowerLawL2Operator hα hlam hs)
  change IsUnit (e (1 - c • boundedPowerLawL2Operator hα hlam hs)) ↔ _ at h
  rw [map_sub, map_one, map_smul] at h
  exact h

/-- A small coupling guarantees invertibility throughout the boundedness range. -/
theorem isUnit_one_sub_smul_powerLawCoefficientOperator_of_norm_lt_one
    {α lam c : ℝ} (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam)
    (hc : |c| *‖boundedPowerLawL2Operator hα hlam hs‖ < 1) :
    IsUnit (1 - c • boundedPowerLawCoefficientOperator hα hlam hs) := by
  apply isUnit_one_sub_of_norm_lt_one
  simpa only [norm_smul, Real.norm_eq_abs, norm_boundedPowerLawCoefficientOperator] using hc

/-- An invertible second-kind operator has a unique physical L² solution for
every right-hand side, throughout the boundedness range. -/
theorem existsUnique_powerLawL2_solution
    {α lam c : ℝ} (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam)
    (hT : IsUnit (1 - c • boundedPowerLawL2Operator hα hlam hs))
    (f : Lp ℝ 2 (gegenbauerMeasure lam)) :
    ∃! u, u - c • boundedPowerLawL2Operator hα hlam hs u = f := by
  have ht := ContinuousLinearMap.isUnit_iff_bijective.mp hT
  obtain ⟨u, hu⟩ := ht.2 f
  have hu' : u - c • boundedPowerLawL2Operator hα hlam hs u = f := by
    simpa only [sub_apply, one_apply_eq_self, smul_apply] using hu
  refine ⟨u, hu', fun v hv ↦ ht.1 ?_⟩
  simpa only [sub_apply, one_apply_eq_self, smul_apply] using hv.trans hu'.symm

variable {α lam : ℝ} (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) < α+lam) (c : ℝ)

/-- Lifted normalized second-kind section; its restriction is the actual finite matrix. -/
def powerLawCoefficientSection (N : ℕ) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  liftedFiniteSection (lp.initialL2Projection N)
    (-(c • boundedPowerLawCoefficientOperator hα hlam hs.le))

variable (hT : IsUnit (1 - c • boundedPowerLawCoefficientOperator hα hlam hs.le))

include hT in
/-- Invertibility of the limiting equation gives eventual section stability. -/
theorem eventually_stable_powerLawCoefficientSection :
    ∀ᶠ N in atTop, IsUnit (powerLawCoefficientSection hα hlam hs c N) ∧
      ‖Ring.inverse (powerLawCoefficientSection hα hlam hs c N)‖ ≤
        ‖Ring.inverse (1 - c • boundedPowerLawCoefficientOperator hα hlam hs.le)‖ + 1 := by
  simpa only [powerLawCoefficientSection, sub_eq_add_neg] using
    eventually_stable_liftedFiniteSection_ringInverse _ lp.norm_initialL2Projection_le
      lp.tendsto_initialL2Projection (-(c • boundedPowerLawCoefficientOperator hα hlam hs.le))
      ((isCompactOperator_boundedPowerLawCoefficientOperator hlam hα hs).smul c).neg
      (by simpa only [sub_eq_add_neg] using hT)

include hT in
/-- The finite normalized projected equations have a unique solution eventually. -/
theorem eventually_existsUnique_powerLaw_projected_solution :
    ∀ᶠ N in atTop, ∀ f : lp (fun _ : ℕ ↦ ℝ) 2,
      ∃! u, lp.initialL2Projection N u = u ∧
        lp.initialL2Projection N (u - c • boundedPowerLawCoefficientOperator hα hlam hs.le u) =
          lp.initialL2Projection N f := by
  filter_upwards [eventually_stable_powerLawCoefficientSection hα hlam hs c hT] with N hN f
  simpa only [add_apply, one_apply_eq_self, _root_.neg_apply, smul_apply, sub_eq_add_neg] using
    existsUnique_projected_solution (lp.initialL2Projection N)
      (-(c • boundedPowerLawCoefficientOperator hα hlam hs.le))
      (lp.initialL2Projection_idempotent N)
      (show IsUnit (liftedFiniteSection (lp.initialL2Projection N)
        (-(c • boundedPowerLawCoefficientOperator hα hlam hs.le))) from hN.1) f

include hT in
/-- Actual finite matrices have unique solutions for all sufficiently large sizes. -/
theorem eventually_existsUnique_powerLaw_matrix_solution :
    ∀ᶠ N in atTop, ∀ f : lp (fun _ : ℕ ↦ ℝ) 2,
      ∃! v : Fin N → ℝ,
        (1 - lp.initialL2Matrix (c • boundedPowerLawCoefficientOperator hα hlam hs.le) N) *ᵥ v =
          (fun i : Fin N ↦ f i) := by
  filter_upwards [eventually_existsUnique_powerLaw_projected_solution hα hlam hs c hT] with N hN f
  exact lp.existsUnique_initialL2Matrix_solution _ N f (hN f)

include hT in
/-- The error is bounded by a section-independent constant times the exact solution tail. -/
theorem eventually_norm_powerLawCoefficientSection_error_le :
    ∀ᶠ N in atTop, ∀ u : lp (fun _ : ℕ ↦ ℝ) 2,
      ‖Ring.inverse (powerLawCoefficientSection hα hlam hs c N)
        (lp.initialL2Projection N (u - c • boundedPowerLawCoefficientOperator hα hlam hs.le u)) - u‖ ≤
        (‖Ring.inverse (1 - c • boundedPowerLawCoefficientOperator hα hlam hs.le)‖ + 1) *
          ‖lp.initialL2Projection N u - u‖ := by
  simpa only [powerLawCoefficientSection, sub_eq_add_neg, add_apply, one_apply_eq_self,
    _root_.neg_apply, smul_apply] using
    eventually_norm_liftedFiniteSection_error_le_ringInverse _ lp.norm_initialL2Projection_le
      lp.tendsto_initialL2Projection (-(c • boundedPowerLawCoefficientOperator hα hlam hs.le))
      ((isCompactOperator_boundedPowerLawCoefficientOperator hlam hα hs).smul c).neg
      (by simpa only [sub_eq_add_neg] using hT)

include hT in
/-- The finite-section solutions converge for every normalized L² right-hand side. -/
theorem tendsto_powerLawCoefficientSection_solution (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N ↦ Ring.inverse (powerLawCoefficientSection hα hlam hs c N)
      (lp.initialL2Projection N f)) atTop
      (𝓝 (Ring.inverse (1 - c • boundedPowerLawCoefficientOperator hα hlam hs.le) f)) := by
  have ht := tendsto_liftedFiniteSection _ lp.norm_initialL2Projection_le
    lp.tendsto_initialL2Projection (-(c • boundedPowerLawCoefficientOperator hα hlam hs.le))
    ((isCompactOperator_boundedPowerLawCoefficientOperator hlam hα hs).smul c).neg
  have hi := tendsto_inverse_of_tendsto ht (by simpa only [sub_eq_add_neg] using hT)
  simpa only [powerLawCoefficientSection, sub_eq_add_neg, Function.comp_def] using
    ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.tendsto _).comp
      (hi.prodMk_nhds (lp.tendsto_initialL2Projection f))

end Real

namespace Real
variable {α lam : ℝ} (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) < α+lam) (c : ℝ)
variable (hT : IsUnit (1-c • boundedPowerLawCoefficientOperator hα hlam hs.le))

theorem powerLaw_inverse_unit_bridge :
    Ring.inverse (1-c • boundedPowerLawCoefficientOperator hα hlam hs.le) =
      (↑(hT.unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2) := by
  simpa only [IsUnit.unit_spec] using Ring.inverse_unit hT.unit

include hT in
theorem invertible_powerLawCoefficientSection_filter_neBot :
    NeBot (Ring.invertibleIndexFilter (powerLawCoefficientSection hα hlam hs c) atTop) :=
  Ring.invertibleIndexFilter_neBot _ _
    ((eventually_stable_powerLawCoefficientSection hα hlam hs c hT).mono (fun _ hn ↦ hn.1))

theorem eventually_stable_powerLawCoefficientSectionOn :
    ∀ᶠ N in atTop, ∃ hN : IsUnit (powerLawCoefficientSection hα hlam hs c N),
      ‖Ring.inverseAt (powerLawCoefficientSection hα hlam hs c) ⟨N,hN⟩‖ ≤
        ‖(↑(hT.unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2)‖+1 := by
  filter_upwards [eventually_stable_powerLawCoefficientSection hα hlam hs c hT] with N hn
  refine ⟨hn.1,?_⟩
  simpa only [Ring.inverseAt_eq_ringInverse,powerLaw_inverse_unit_bridge hα hlam hs c hT] using hn.2

theorem eventually_norm_powerLawCoefficientSection_error_leOn :
    ∀ᶠ N in atTop, ∃ hN : IsUnit (powerLawCoefficientSection hα hlam hs c N),
      ∀ u : lp (fun _ : ℕ ↦ ℝ) 2,
      ‖Ring.inverseAt (powerLawCoefficientSection hα hlam hs c) ⟨N,hN⟩
        (lp.initialL2Projection N (u-c • boundedPowerLawCoefficientOperator hα hlam hs.le u))-u‖ ≤
        (‖(↑(hT.unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2)‖+1)*
          ‖lp.initialL2Projection N u-u‖ := by
  filter_upwards [eventually_stable_powerLawCoefficientSection hα hlam hs c hT,
    eventually_norm_powerLawCoefficientSection_error_le hα hlam hs c hT] with N hn he
  refine ⟨hn.1,fun u ↦ ?_⟩
  simpa only [Ring.inverseAt_eq_ringInverse,powerLaw_inverse_unit_bridge hα hlam hs c hT] using he u

theorem tendsto_powerLawCoefficientSection_solutionOn (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N : Ring.InvertibleIndex (powerLawCoefficientSection hα hlam hs c) ↦
      Ring.inverseAt (powerLawCoefficientSection hα hlam hs c) N (lp.initialL2Projection N f))
      (Ring.invertibleIndexFilter (powerLawCoefficientSection hα hlam hs c) atTop)
      (𝓝 ((↑(hT.unit⁻¹) : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2) f)) := by
  have h := (tendsto_powerLawCoefficientSection_solution hα hlam hs c hT f).comp
    (Filter.tendsto_comap : Tendsto
      (Subtype.val : Ring.InvertibleIndex (powerLawCoefficientSection hα hlam hs c) → ℕ)
      (Filter.comap Subtype.val atTop) atTop)
  simpa only [Ring.invertibleIndexFilter,Function.comp_def,Ring.inverseAt_eq_ringInverse,
    powerLaw_inverse_unit_bridge hα hlam hs c hT] using h
end Real
