/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.MeasureTheory.Integral.ClassicalWeight
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Measure

/-! # Classical semiclassical Jacobi integration
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- Finite mass, all moments, strict positivity and orthogonal sequences in the
full classical parameter range of PGSO Section 3. -/
theorem semiclassicalJacobiMeasure_foundation (t : Ioi (1 : ℝ))
    {α β γ : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IsFiniteMeasure (semiclassicalJacobiMeasure t α β γ) ∧
      HasFiniteMoments (semiclassicalJacobiMeasure t α β γ) ∧
      HasPositiveDefiniteIntegral (semiclassicalJacobiMeasure t α β γ) ∧
      ∃ P : Sequence ℝ, P.IsOrthogonal (semiclassicalJacobiMeasure t α β γ) := by
  exact ⟨isFiniteMeasure_semiclassicalJacobiMeasure t.property hα hβ,
    hasFiniteMoments_semiclassicalJacobiMeasure t.property hα hβ,
    hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure t.property hα hβ,
    exists_isOrthogonal_semiclassicalJacobiMeasure t.property hα hβ⟩

/-- The density has a finite integral under precisely the stated admissible exponents. -/
theorem integrable_semiclassicalJacobiWeight (t : Ioi (1 : ℝ))
    {α β γ : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    Integrable (fun x : Ioo (0 : ℝ) 1 ↦ (semiclassicalJacobiWeight t α β γ x : ℝ)) volume := by
  have := (semiclassicalJacobiMeasure_foundation t (γ := γ) hα hβ).1
  simpa using (integrable_semiclassicalJacobiMeasure_iff t α β γ
    (fun _ ↦ 1)).1 (integrable_const 1)

end Polynomial
