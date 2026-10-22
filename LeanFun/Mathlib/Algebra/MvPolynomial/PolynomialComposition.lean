/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Univariate polynomials composed with multivariate polynomials
Evaluation and degree bounds for radial and separated constructions.
Reference: polynomial composition, used in DLMF 18.37.
-/

public section
namespace MvPolynomial
variable {R σ : Type*} [CommSemiring R]

/-- Evaluation commutes with univariate polynomial composition. -/
theorem eval_polynomial_eval₂_C (p : Polynomial R) (q : MvPolynomial σ R) (v : σ → R) :
    eval v (p.eval₂ C q) = p.eval (eval v q) := by
  have hc : (eval v).comp C = RingHom.id R := by ext r; simp
  rw [Polynomial.hom_eval₂, hc]
  rfl

/-- Composition multiplies the available degree bounds. -/
theorem totalDegree_polynomial_eval₂_C_le (p : Polynomial R) (q : MvPolynomial σ R) :
    (p.eval₂ C q).totalDegree ≤ p.natDegree*q.totalDegree := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro j hj
  have hjn : j ≤ p.natDegree := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  exact (totalDegree_mul _ _).trans (by
    simpa only [totalDegree_C, zero_add] using
      (totalDegree_pow q j).trans (Nat.mul_le_mul_right q.totalDegree hjn))

end MvPolynomial
