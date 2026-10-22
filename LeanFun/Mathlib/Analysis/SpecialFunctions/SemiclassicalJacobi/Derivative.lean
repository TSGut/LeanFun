/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DerivativeSupport
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Basis

/-! # Exact sparse differentiation on semiclassical coefficients
Use the existing polynomial derivative linear map and basis coefficient action.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.4.
-/

@[expose] public section
open Module
namespace Polynomial

/-- The derivative matrix from the original to the simultaneously raised family. -/
noncomputable def semiclassicalJacobiDerivative {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα1 : -1 < α+1) (hβ1 : -1 < β+1) : Matrix ℕ ℕ ℝ :=
  (semiclassicalJacobiBasis ht hα1 hβ1 (γ+1)).toMatrix
    (fun n ↦ (semiclassicalJacobiSequence ht hα hβ γ n).derivative)

/-- Column n of the actual derivative matrix is supported only at n-1 and n-2. -/
theorem semiclassicalJacobiDerivative_eq_zero {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα1 : -1 < α+1) (hβ1 : -1 < β+1) (n j : ℕ)
    (hgap : n ≤ j ∨ j+2 < n) :
    semiclassicalJacobiDerivative ht hα hβ γ hα1 hβ1 j n = 0 := by
  rw [semiclassicalJacobiDerivative, Basis.toMatrix_apply, semiclassicalJacobiBasis_repr]
  exact integralInner_semiclassicalJacobi_derivative_eq_zero ht hα hβ hα1 hβ1 n j hgap

/-- The coefficient operator differentiates every finite polynomial expansion exactly. -/
theorem semiclassicalJacobi_derivative_coefficientMap_exact {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα1 : -1 < α+1) (hβ1 : -1 < β+1) (v : ℕ →₀ ℝ) :
    (semiclassicalJacobiBasis ht hα1 hβ1 (γ+1)).repr.symm
      ((semiclassicalJacobiBasis ht hα hβ γ).coefficientMap
        (semiclassicalJacobiBasis ht hα1 hβ1 (γ+1)) derivative v) =
      ((semiclassicalJacobiBasis ht hα hβ γ).repr.symm v).derivative :=
  Basis.repr_symm_coefficientMap _ _ _ _

/-- The sparse matrix acts by a finite sum over input coefficients. -/
theorem semiclassicalJacobi_derivative_coefficientMap_apply {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα1 : -1 < α+1) (hβ1 : -1 < β+1) (v : ℕ →₀ ℝ) (i : ℕ) :
    (semiclassicalJacobiBasis ht hα hβ γ).coefficientMap
        (semiclassicalJacobiBasis ht hα1 hβ1 (γ+1)) derivative v i =
      v.sum (fun j a ↦ semiclassicalJacobiDerivative ht hα hβ γ hα1 hβ1 i j * a) := by
  rw [Basis.coefficientMap_apply]
  simp only [semiclassicalJacobiDerivative, semiclassicalJacobiBasis_apply]

end Polynomial
