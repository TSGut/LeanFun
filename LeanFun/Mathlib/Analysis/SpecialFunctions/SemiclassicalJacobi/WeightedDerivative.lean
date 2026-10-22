/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Derivative

/-! # Weighted differentiation in the semiclassical hierarchy
The polynomial adjoint sigma*q'+tau*q represents differentiating the raised
weight times q, then dividing by the original weight. Integration by parts
identifies its matrix with minus the transpose of unweighted differentiation.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.4.
-/

@[expose] public section
open Module
namespace Polynomial

/-- The exact polynomial action of weighted differentiation. -/
noncomputable def semiclassicalJacobiWeightedDerivativeMap (t α β γ : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (LinearMap.mulLeft ℝ (semiclassicalJacobiSigma t)).comp derivative +
    LinearMap.mulLeft ℝ (semiclassicalJacobiTau t α β γ)

/-- The weighted derivative matrix from the raised family back to the original family. -/
noncomputable def semiclassicalJacobiWeightedDerivative {t α β : ℝ} (ht : 1<t)
    (hα : -1<α) (hβ : -1<β) (γ : ℝ) (hα1 : -1<α+1) (hβ1 : -1<β+1) : Matrix ℕ ℕ ℝ :=
  (semiclassicalJacobiBasis ht hα hβ γ).toMatrix (fun j ↦
    semiclassicalJacobiWeightedDerivativeMap t α β γ
      (semiclassicalJacobiSequence ht hα1 hβ1 (γ+1) j))

/-- The two differentiation matrices are negative transposes with these orthonormal scalings. -/
theorem semiclassicalJacobiWeightedDerivative_eq_neg_transpose {t α β : ℝ} (ht : 1<t)
    (hα : -1<α) (hβ : -1<β) (γ : ℝ) (hα1 : -1<α+1) (hβ1 : -1<β+1) :
    semiclassicalJacobiWeightedDerivative ht hα hβ γ hα1 hβ1 =
      -(semiclassicalJacobiDerivative ht hα hβ γ hα1 hβ1).transpose := by
  ext n j
  simp only [semiclassicalJacobiWeightedDerivative, semiclassicalJacobiDerivative,
    Basis.toMatrix_apply, semiclassicalJacobiBasis_repr, Matrix.neg_apply, Matrix.transpose_apply]
  rw [integralInner_semiclassicalJacobi_derivative ht hα hβ, neg_neg, integralInner_comm]
  rfl

/-- Column j of weighted differentiation has support only at j+1 and j+2. -/
theorem semiclassicalJacobiWeightedDerivative_eq_zero {t α β : ℝ} (ht : 1<t)
    (hα : -1<α) (hβ : -1<β) (γ : ℝ) (hα1 : -1<α+1) (hβ1 : -1<β+1)
    (n j : ℕ) (hgap : n≤j ∨ j+2<n) :
    semiclassicalJacobiWeightedDerivative ht hα hβ γ hα1 hβ1 n j=0 := by
  rw [semiclassicalJacobiWeightedDerivative_eq_neg_transpose]
  simp only [Matrix.neg_apply, Matrix.transpose_apply,
    semiclassicalJacobiDerivative_eq_zero ht hα hβ γ hα1 hβ1 n j hgap, neg_zero]

/-- Weighted differentiation acts exactly on every finite expansion. -/
theorem semiclassicalJacobi_weightedDerivative_coefficientMap_exact {t α β : ℝ} (ht : 1<t)
    (hα : -1<α) (hβ : -1<β) (γ : ℝ) (hα1 : -1<α+1) (hβ1 : -1<β+1) (v : ℕ →₀ ℝ) :
    (semiclassicalJacobiBasis ht hα hβ γ).repr.symm
      ((semiclassicalJacobiBasis ht hα1 hβ1 (γ+1)).coefficientMap
        (semiclassicalJacobiBasis ht hα hβ γ) (semiclassicalJacobiWeightedDerivativeMap t α β γ) v) =
      semiclassicalJacobiWeightedDerivativeMap t α β γ
        ((semiclassicalJacobiBasis ht hα1 hβ1 (γ+1)).repr.symm v) :=
  Basis.repr_symm_coefficientMap _ _ _ _

end Polynomial
