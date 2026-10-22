/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.FiniteConnection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Operators

/-!
# Jacobi connections in the full orthogonality range

The target coefficient matrix is nonsingular for every alpha,beta > -1.
Source parameters are unrestricted. Reference: DLMF 18.18(iv).
-/

public section
namespace Polynomial

/-- Positivity of target leading coefficients makes the finite determinant positive. -/
theorem det_jacobiConnectionMatrix_pos {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (N : ℕ) :
    0 < (jacobiConnectionMatrix α β N).det := by
  rw [jacobiConnectionMatrix, det_connectionMatrix _ (fun j ↦ natDegree_jacobi_le α β j)]
  exact Finset.prod_pos (fun j _ ↦ coeff_jacobi_self_pos hα hβ j)

/-- Arbitrary real Jacobi parameters expand into every target in the full
orthogonality range, with the explicit finite determinant coefficients. -/
theorem jacobi_eq_sum_finiteConnectionCoefficient_of_neg_one_lt {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (γ δ : ℝ) (N : ℕ) :
    jacobi γ δ N =
      ∑ j : Fin (N + 1), jacobiFiniteConnectionCoefficient α β γ δ N j ⟨(det_jacobiConnectionMatrix_pos hα hβ N).ne'⟩ • jacobi α β j :=
  jacobi_eq_sum_finiteConnectionCoefficient α β γ δ N (det_jacobiConnectionMatrix_pos hα hβ N).ne'

/-- Determinant coefficients agree with the existing polynomial-basis coordinates. -/
theorem jacobiFiniteConnectionCoefficient_eq_repr {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (γ δ : ℝ) (N : ℕ) (j : Fin (N + 1)) :
    jacobiFiniteConnectionCoefficient α β γ δ N j ⟨(det_jacobiConnectionMatrix_pos hα hβ N).ne'⟩ =
      (jacobiBasis hα hβ).repr (jacobi γ δ N) j := by
  have he := congrArg (fun p : ℝ[X] ↦ (jacobiBasis hα hβ).repr p j)
    (jacobi_eq_sum_finiteConnectionCoefficient_of_neg_one_lt hα hβ γ δ N)
  have hr (i : Fin (N + 1)) :
      (jacobiBasis hα hβ).repr (jacobi α β i) = Finsupp.single (i : ℕ) 1 := by
    rw [← jacobiBasis_apply hα hβ, Module.Basis.repr_self]
  simp only [map_sum, map_smul, hr, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at he
  simpa only [← Fin.ext_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using he.symm

end Polynomial
