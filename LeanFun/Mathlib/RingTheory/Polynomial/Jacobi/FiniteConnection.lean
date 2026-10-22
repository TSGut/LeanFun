/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi
public import LeanFun.Mathlib.LinearAlgebra.Polynomial.FiniteConnection

/-!
# Finite connections between arbitrary Jacobi families

The formulas use finite determinants of monomial coefficients. The multiplied
identity includes degenerate parameters; divided coefficients require only
nondegeneracy of the target family through the source degree. Compact classical
Pochhammer formulas are a separate result. References: DLMF 18.18(iv); Cramer's rule.
-/

@[expose] public section
namespace Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The coefficient matrix of the first `N+1` target Jacobi polynomials. -/
noncomputable def jacobiConnectionMatrix (α β : R) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  connectionMatrix (fun j : Fin (N + 1) ↦ jacobi α β j)

/-- Explicit determinant numerators for changing both Jacobi parameters. -/
noncomputable def jacobiConnectionNumerator (α β γ δ : R) (N : ℕ) : Fin (N + 1) → R :=
  connectionNumerator (fun j : Fin (N + 1) ↦ jacobi α β j) (jacobi γ δ N)

/-- The common connection denominator is the product of the degree-`j` coefficients
of the target Jacobi polynomials, including degree-dropping specialisations
(DLMF Table 18.3.1). -/
theorem det_jacobiConnectionMatrix (α β : R) (N : ℕ) :
    (jacobiConnectionMatrix α β N).det =
      ∏ j : Fin (N + 1), algebraMap ℚ R (((j.val.factorial : ℚ) * 2 ^ j.val)⁻¹) *
        (ascPochhammer R j.val).eval ((j.val : R) + α + β + 1) := by
  rw [jacobiConnectionMatrix, det_connectionMatrix _ (fun j ↦ natDegree_jacobi_le α β j)]
  simp only [coeff_jacobi_self]

/-- A universal finite connection identity between arbitrary Jacobi parameters,
with the determinant denominator cleared, including singular specialisations. -/
theorem det_smul_jacobi_eq_sum_connectionNumerator (α β γ δ : R) (N : ℕ) :
    (jacobiConnectionMatrix α β N).det • jacobi γ δ N =
      ∑ j : Fin (N + 1), jacobiConnectionNumerator α β γ δ N j • jacobi α β j := by
  apply det_smul_eq_sum_connectionNumerator
  · intro j
    exact (degree_jacobi_le α β j).trans_lt (Nat.cast_lt.mpr j.isLt)
  · exact (degree_jacobi_le γ δ N).trans_lt (Nat.cast_lt.mpr (Nat.lt_succ_self N))

section Field
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Finite determinant connection coefficients in the original Jacobi normalisation. -/
noncomputable def jacobiFiniteConnectionCoefficient (α β γ δ : K) (N : ℕ)
    (j : Fin (N + 1)) (_d : FiniteConnectionInput (fun i : Fin (N+1) => jacobi α β i)) : K :=
  jacobiConnectionNumerator α β γ δ N j / (jacobiConnectionMatrix α β N).det

/-- The classical coefficient recovers its determinant numerator. -/
theorem jacobiFiniteConnectionCoefficient_mul_det (α β γ δ : K) (N : ℕ)
    (j : Fin (N+1)) (d : FiniteConnectionInput (fun i : Fin (N+1) => jacobi α β i)) :
    jacobiFiniteConnectionCoefficient α β γ δ N j d * (jacobiConnectionMatrix α β N).det =
      jacobiConnectionNumerator α β γ δ N j :=
  div_mul_cancel₀ _ d.nonsingular

/-- The finite Jacobi expansion when the target determinant is nonzero.
No nondegeneracy condition is imposed on the source parameters. -/
theorem jacobi_eq_sum_finiteConnectionCoefficient (α β γ δ : K) (N : ℕ)
    (hd : (jacobiConnectionMatrix α β N).det ≠ 0) :
    jacobi γ δ N =
      ∑ j : Fin (N + 1), jacobiFiniteConnectionCoefficient α β γ δ N j ⟨hd⟩ • jacobi α β j := by
  exact eq_sum_finiteConnectionCoefficient _ _
    (fun j ↦ (degree_jacobi_le α β j).trans_lt (Nat.cast_lt.mpr j.isLt))
    ((degree_jacobi_le γ δ N).trans_lt (Nat.cast_lt.mpr (Nat.lt_succ_self N))) hd

end Field
end Polynomial
