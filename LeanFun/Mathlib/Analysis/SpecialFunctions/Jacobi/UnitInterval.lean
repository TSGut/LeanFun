/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Shifted
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.DiskOuterMeasure
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Ring

/-! # Affine Jacobi measures on the unit interval
This is the pushforward under t -> (t+1)/2, preserving the original Jacobi mass.
Its Lebesgue density therefore includes the factor 2^(alpha+beta+1).
Reference: affine transport of DLMF Table 18.3.1 and the triangle formula 18.37.7.
-/

@[expose] public section
open MeasureTheory Set
namespace Polynomial

/-- Jacobi measure transported to [0,1], with its original total mass. -/
noncomputable def unitJacobiMeasure (α β : ℝ) : Measure ℝ :=
  Measure.map (fun t : ℝ ↦ (t + 1) / 2) (jacobiMeasure α β)

/-- Integration against the affine pushforward for a certified integrable input. -/
theorem integral_unitJacobiMeasure (α β : ℝ) (f : IntegrableInput (unitJacobiMeasure α β)) :
    ∫ x, f.val x ∂unitJacobiMeasure α β = ∫ t, f.val ((t + 1) / 2) ∂jacobiMeasure α β := by
  exact integral_map (by fun_prop) f.integrable.aestronglyMeasurable

/-- Finite mass is preserved by the affine map. -/
theorem isFiniteMeasure_unitJacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IsFiniteMeasure (unitJacobiMeasure α β) := by
  let := isFiniteMeasure_jacobiMeasure hα hβ
  unfold unitJacobiMeasure
  infer_instance

/-- The affine Jacobi measure is supported on the closed unit interval. -/
theorem ae_mem_Icc_unitJacobiMeasure (α β : ℝ) :
    ∀ᵐ x ∂unitJacobiMeasure α β, x ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).2
  filter_upwards [ae_mem_Icc_jacobiMeasure α β] with t ht
  change 0 ≤ (t + 1) / 2 ∧ (t + 1) / 2 ≤ 1
  constructor <;> linarith [ht.1, ht.2]

/-- Affine transport gives the original Jacobi pairings exactly. -/
theorem integralInner_shiftedJacobi (α β : ℝ) (n m : ℕ)
    (hi : Integrable (fun x => (jacobi α β n).eval x * (jacobi α β m).eval x)
      (jacobiMeasure α β) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (unitJacobiMeasure α β) (IntegrablePair.of (unitJacobiMeasure α β) (shiftedJacobi α β n) (shiftedJacobi α β m) (h := by
        rw [unitJacobiMeasure, integrable_map_measure (by fun_prop) (by fun_prop)]
        simpa only [Function.comp_def, eval_shiftedJacobi_half_add_one] using hi)) =
      integralInner (jacobiMeasure α β) (IntegrablePair.of (jacobiMeasure α β) (jacobi α β n) (jacobi α β m)) := by
  simp only [integralInner]
  rw [integral_unitJacobiMeasure _ _ ⟨_, by
    rw [unitJacobiMeasure, integrable_map_measure (by fun_prop) (by fun_prop)]
    simpa only [Function.comp_def, eval_shiftedJacobi_half_add_one] using hi⟩]
  simp only [eval_shiftedJacobi_half_add_one]

/-- Every polynomial has finite square integral after affine transport. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_unitJacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    HasFiniteMoments (unitJacobiMeasure α β) := by
  intro p
  rw [unitJacobiMeasure, integrable_map_measure (by fun_prop) (by fun_prop)]
  convert hasFiniteMoments_jacobiMeasure hα hβ (p.comp ((X + 1) * C (1 / 2))) using 1
  ext t
  simp [eval_comp, div_eq_mul_inv]

end Polynomial
