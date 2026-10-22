/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Normalization

/-! # Positive orthonormal semiclassical Jacobi sequences
The degree-indexed sequence uses the general orthogonal-polynomial construction,
with positive leading coefficients and unit norms. Reference: Papadopoulos–Gutleb–
Slevinsky–Olver, semiclassical Jacobi hierarchies, Section 3.
-/

@[expose] public section
open MeasureTheory
namespace Polynomial

/-- The positive-leading orthonormal semiclassical Jacobi family. -/
noncomputable def semiclassicalJacobiSequence {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) : Sequence ℝ :=
  (exists_positive_orthonormal_sequence (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ)
    (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
    (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα hβ)).choose

/-- Orthogonality, positive leading coefficients and squared norms characterize the scaling. -/
theorem semiclassicalJacobiSequence_spec {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) :
    (semiclassicalJacobiSequence ht hα hβ γ).IsOrthogonal (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) ∧
    (∀ n, 0 < (semiclassicalJacobiSequence ht hα hβ γ n).leadingCoeff) ∧
    (∀ n, ∫ x, (semiclassicalJacobiSequence ht hα hβ γ n).eval x ^ 2
      ∂semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ = 1) :=
  (exists_positive_orthonormal_sequence (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ)
    (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
    (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα hβ)).choose_spec

end Polynomial
