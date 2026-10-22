/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskLift

/-!
# Vertical polynomial truncation

A univariate polynomial truncated at degree `n`, embedded in the second variable.
The homogeneous evaluation identity preserves the algebraic zero-step case of
separated polynomial constructions without dividing by zero.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, §2.6.1.
-/

@[expose] public section
namespace MvPolynomial
variable {R : Type*} [CommRing R]
/-- Truncate a univariate coefficient expansion and regard it as a polynomial in `y`.
This is the classical polynomial content of the zero-step separated lift. -/
noncomputable def verticalTruncation (n : ℕ) (p : Polynomial R) : MvPolynomial (Fin 2) R :=
  ∑ j ∈ Finset.range (n + 1), C (p.coeff j) * X 1 ^ j

/-- Truncation retains evaluation when the degree is within the cutoff. -/
theorem eval_verticalTruncation (n : ℕ) (p : Polynomial R) (hp : p.natDegree ≤ n)
    (v : Fin 2 → R) : eval v (verticalTruncation n p) = p.eval (v 1) := by
  rw [verticalTruncation, map_sum, Polynomial.eval_eq_sum_range' (by omega : p.natDegree < n+1)]
  simp

/-- A single supported degree scales homogeneously, including at zero scale. -/
theorem eval_verticalTruncation_homogeneous (n : ℕ) (p : Polynomial R)
    (hp : p.natDegree ≤ n) (hpar : ∀ j ≤ n, p.coeff j ≠ 0 → j = n)
    (v : Fin 2 → R) (s z : R) (hy : v 1 = s * z) :
    eval v (verticalTruncation n p) = s^n * p.eval z := by
  rw [verticalTruncation, map_sum, Polynomial.eval_eq_sum_range' (by omega : p.natDegree < n+1),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, map_pow, eval_C, eval_X, hy]
  by_cases hz : p.coeff j = 0
  · simp [hz]
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  rw [hpar j hjn hz, mul_pow]
  ring

/-- Coefficient truncation bounds the total degree over any commutative ring. -/
theorem totalDegree_verticalTruncation_le (n : ℕ) (p : Polynomial R) :
    (verticalTruncation n p).totalDegree ≤ n := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    rw [Subsingleton.elim (verticalTruncation n p) 0, totalDegree_zero]
    exact Nat.zero_le _
  let := hR
  unfold verticalTruncation
  apply totalDegree_finsetSum_le
  intro j hj
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  exact (totalDegree_mul _ _).trans (by simpa using hjn)
end MvPolynomial
