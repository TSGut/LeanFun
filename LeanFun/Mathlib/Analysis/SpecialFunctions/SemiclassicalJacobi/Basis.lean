/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Sequence
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Recurrence
public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap

/-! # Orthonormal coefficient coordinates for semiclassical Jacobi polynomials
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.
-/

@[expose] public section
open MeasureTheory Module
namespace Polynomial

/-- The positive orthonormal semiclassical sequence as a polynomial basis. -/
noncomputable def semiclassicalJacobiBasis {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) : Basis ℕ ℝ ℝ[X] :=
  (semiclassicalJacobiSequence ht hα hβ γ).basis (fun n ↦
    isUnit_iff_ne_zero.mpr ((semiclassicalJacobiSequence_spec ht hα hβ γ).2.1 n).ne')

@[simp] theorem semiclassicalJacobiBasis_apply {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (n : ℕ) :
    semiclassicalJacobiBasis ht hα hβ γ n = semiclassicalJacobiSequence ht hα hβ γ n :=
  (semiclassicalJacobiSequence ht hα hβ γ).basis_eq_self _ n

/-- Coefficient coordinates are integral projections, since the basis is normalized. -/
theorem semiclassicalJacobiBasis_repr {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (p : ℝ[X]) (n : ℕ) :
    (semiclassicalJacobiBasis ht hα hβ γ).repr p n =
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) p (semiclassicalJacobiSequence ht hα hβ γ n)) := by
  rw [semiclassicalJacobiBasis,
    (semiclassicalJacobiSequence_spec ht hα hβ γ).1.basis_repr_eq_integralInner_div
      (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
      (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα hβ)]
  rw [integralInner_self, (semiclassicalJacobiSequence_spec ht hα hβ γ).2.2 n, div_one]

end Polynomial
