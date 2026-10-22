/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.PartialWeightedDerivativeSupport
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Basis

/-! # Exact partial weighted differentiation on semiclassical coefficients
The external parameter decreases by one while both endpoint parameters increase.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.4.
-/

@[expose] public section
open Module
namespace Polynomial

/-- The derivative matrix from the original to the endpoint-raised family. -/
noncomputable def semiclassicalJacobiCWeightedDerivative {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα1 : -1 < α+1) (hβ1 : -1 < β+1) : Matrix ℕ ℕ ℝ :=
  (semiclassicalJacobiBasis ht hα1 hβ1 γ).toMatrix
    (fun n ↦ semiclassicalJacobiCWeightedDerivativeMap t γ
      (semiclassicalJacobiSequence ht hα hβ (γ+1) n))

/-- Column n of the actual derivative matrix is supported only at n-1 and n-2. -/
theorem semiclassicalJacobiCWeightedDerivative_eq_zero {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα1 : -1 < α+1) (hβ1 : -1 < β+1) (n j : ℕ)
    (hgap : n < j ∨ j+1 < n) :
    semiclassicalJacobiCWeightedDerivative ht hα hβ γ hα1 hβ1 j n = 0 := by
  rw [semiclassicalJacobiCWeightedDerivative, Basis.toMatrix_apply, semiclassicalJacobiBasis_repr]
  exact integralInner_semiclassicalJacobi_cWeightedDerivative_eq_zero ht hα hβ hα1 hβ1 n j hgap

/-- The coefficient operator acts on every finite polynomial expansion exactly. -/
theorem semiclassicalJacobi_cWeightedDerivative_coefficientMap_exact {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα1 : -1 < α+1) (hβ1 : -1 < β+1) (v : ℕ →₀ ℝ) :
    (semiclassicalJacobiBasis ht hα1 hβ1 γ).repr.symm
      ((semiclassicalJacobiBasis ht hα hβ (γ+1)).coefficientMap
        (semiclassicalJacobiBasis ht hα1 hβ1 γ) (semiclassicalJacobiCWeightedDerivativeMap t γ) v) =
      semiclassicalJacobiCWeightedDerivativeMap t γ
        ((semiclassicalJacobiBasis ht hα hβ (γ+1)).repr.symm v) :=
  Basis.repr_symm_coefficientMap _ _ _ _

/-- The sparse matrix acts by a finite sum over input coefficients. -/
theorem semiclassicalJacobi_cWeightedDerivative_coefficientMap_apply {t α β : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα1 : -1 < α+1) (hβ1 : -1 < β+1) (v : ℕ →₀ ℝ) (i : ℕ) :
    (semiclassicalJacobiBasis ht hα hβ (γ+1)).coefficientMap
        (semiclassicalJacobiBasis ht hα1 hβ1 γ) (semiclassicalJacobiCWeightedDerivativeMap t γ) v i =
      v.sum (fun j a ↦ semiclassicalJacobiCWeightedDerivative ht hα hβ γ hα1 hβ1 i j * a) := by
  rw [Basis.coefficientMap_apply]
  simp only [semiclassicalJacobiCWeightedDerivative, semiclassicalJacobiBasis_apply]

end Polynomial
