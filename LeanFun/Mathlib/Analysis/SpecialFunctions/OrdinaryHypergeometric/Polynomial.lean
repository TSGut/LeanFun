/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.Domain
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Operations
/-! # Classical terminating Gauss polynomials
All denominator factors before termination are genuine nonzero values.
Earlier termination by either numerator is retained. Reference: DLMF15.2.4--5.
-/
@[expose] public noncomputable section
open Polynomial Finset
section PolynomialValues
variable {K : Type*} [RCLike K]
/-- Admissible terminating Gauss parameters, retaining possible earlier termination. -/
abbrev TerminatingGaussParameters (K : Type*) [RCLike K] (k : ℕ) :=
  {p : GaussParameters K // p.b = -(k : K)}

/-- Non-pole denominator parameters give admissible terminating polynomials. -/
def TerminatingGaussParameters.ofNoPole (a c : K) (k : ℕ)
    (hc : ∀ n : ℕ, c ≠ -(n : K)) : TerminatingGaussParameters K k :=
  ⟨GaussParameters.ofNoPole a (-(k : K)) c hc, rfl⟩

/-- The classical terminating Gauss polynomial. Reference: DLMF 15.2.4--5. -/
def ordinaryHypergeometricPolynomial (k : ℕ) (p : TerminatingGaussParameters K k) : K[X] :=
  ∑ n ∈ Finset.range (k + 1), Polynomial.C (ordinaryHypergeometricCoefficientOn p.val n) * Polynomial.X ^ n

/-- The classical terminating function equals its polynomial at every argument. -/
theorem ordinaryHypergeometric_eq_eval_polynomial (k : ℕ)
    (p : TerminatingGaussParameters K k) (z : K) :
    ordinaryHypergeometricOn p.val (.ofTerminating p.val k (Or.inr p.property) z) =
      (ordinaryHypergeometricPolynomial k p).eval z := by
  rw [ordinaryHypergeometricOn_terminating]
  simp only [ordinaryHypergeometricPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- The degree bound includes earlier termination by either numerator parameter. -/
theorem natDegree_ordinaryHypergeometricPolynomial_le (k : ℕ)
    (p : TerminatingGaussParameters K k) :
    (ordinaryHypergeometricPolynomial k p).natDegree ≤ k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by simpa using hn)


end PolynomialValues
