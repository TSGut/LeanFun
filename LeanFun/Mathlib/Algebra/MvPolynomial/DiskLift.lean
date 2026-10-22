/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial lifting for Cartesian disk families

For a degree-at-most-n polynomial of parity n, the coefficient formula realizes
`s^n p(y/s)` with `s^2 = 1-x^2` as an actual bivariate polynomial. Its definition
uses neither division nor square roots, and therefore also defines boundary values.

Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, disk construction.
-/

@[expose] public section
namespace MvPolynomial
variable {R : Type*} [CommRing R]

/-- The parity lift used by Cartesian disk polynomials. Its separated-function
interpretation requires the input polynomial to have parity `n`. -/
noncomputable def diskLift (n : ℕ) (p : Polynomial R) : MvPolynomial (Fin 2) R :=
  ∑ j ∈ Finset.range (n + 1),
    C (p.coeff j) * X 1 ^ j * (1 - X 0 ^ 2) ^ ((n - j) / 2)

/-- Evaluating the lift after a squared-radius substitution is exactly the
scaled univariate polynomial, with no invertibility assumption on the radius. -/
theorem eval_diskLift_scaled (n : ℕ) (p : Polynomial R)
    (hp : p.natDegree ≤ n) (hpar : ∀ j, j % 2 ≠ n % 2 → p.coeff j = 0)
    (v : Fin 2 → R) (s z : R) (hs : 1 - v 0 ^ 2 = s ^ 2) (hy : v 1 = s * z) :
    eval v (diskLift n p) = s ^ n * p.eval z := by
  rw [diskLift, map_sum, Polynomial.eval_eq_sum_range' (by omega : p.natDegree < n + 1),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, map_pow, map_sub, map_one, eval_C, eval_X, hs, hy]
  by_cases hjpar : j % 2 = n % 2
  · have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    have he : j + 2 * ((n - j) / 2) = n := by omega
    rw [mul_pow, ← pow_mul]
    calc
      p.coeff j * (s ^ j * z ^ j) * s ^ (2 * ((n - j) / 2)) =
          (s ^ j * s ^ (2 * ((n - j) / 2))) * (p.coeff j * z ^ j) := by ring
      _ = s ^ n * (p.coeff j * z ^ j) := by rw [← pow_add, he]
  · simp [hpar j hjpar]

/-- Lifting does not exceed its specified total degree. -/
theorem totalDegree_diskLift_le (n : ℕ) (p : Polynomial R) :
    (diskLift n p).totalDegree ≤ n := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    rw [Subsingleton.elim (diskLift n p) 0, totalDegree_zero]
    exact Nat.zero_le _
  let := hR
  unfold diskLift
  apply totalDegree_finsetSum_le
  intro j hj
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hb : (1 - (X 0 : MvPolynomial (Fin 2) R) ^ 2).totalDegree ≤ 2 := by
    have hx : ((X (0 : Fin 2) : MvPolynomial (Fin 2) R) ^ 2).totalDegree = 2 :=
      totalDegree_X_pow (0 : Fin 2) 2
    exact (totalDegree_sub (1 : MvPolynomial (Fin 2) R) (X 0 ^ 2)).trans
      (by rw [totalDegree_one, hx]; exact le_refl _)
  have hp := totalDegree_pow (1 - (X 0 : MvPolynomial (Fin 2) R) ^ 2) ((n - j) / 2)
  have hc : (C (p.coeff j) * (X 1 : MvPolynomial (Fin 2) R) ^ j).totalDegree ≤ j := by
    simpa using totalDegree_mul (C (p.coeff j)) (X 1 ^ j : MvPolynomial (Fin 2) R)
  have ht := totalDegree_mul
    (C (p.coeff j) * (X 1 : MvPolynomial (Fin 2) R) ^ j)
    ((1 - X 0 ^ 2) ^ ((n - j) / 2))
  have hh := Nat.mul_le_mul_left ((n - j) / 2) hb
  omega

/-- Embedding a univariate polynomial in one coordinate preserves its degree bound. -/
theorem totalDegree_eval₂_C_X_le {σ : Type*} (p : Polynomial R) (i : σ) :
    (p.eval₂ C (X i : MvPolynomial σ R)).totalDegree ≤ p.natDegree := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    rw [Subsingleton.elim (p.eval₂ C (X i : MvPolynomial σ R)) 0, totalDegree_zero]
    exact Nat.zero_le _
  let := hR
  rw [Polynomial.eval₂_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro j hj
  have hjn : j ≤ p.natDegree := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  exact (totalDegree_mul _ _).trans (by simpa using hjn)

/-- Increasing the lift degree by two multiplies a lower-degree input by the
boundary polynomial `1-x²`. This is the step used in disk parameter raising. -/
theorem diskLift_add_two (n : ℕ) (p : Polynomial R) (hp : p.natDegree ≤ n) :
    diskLift (n + 2) p = (1 - X 0 ^ 2) * diskLift n p := by
  unfold diskLift
  rw [show n + 2 + 1 = (n + 1) + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n + 1),
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n + 1 + 1)]
  simp only [map_zero, zero_mul, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have he : (n + 2 - j) / 2 = (n - j) / 2 + 1 := by omega
  rw [he, pow_succ]
  ring

/-- The lift is linear in the input polynomial at fixed parity degree. -/
theorem diskLift_add (n : ℕ) (p q : Polynomial R) :
    diskLift n (p + q) = diskLift n p + diskLift n q := by
  simp [diskLift, map_add, add_mul, Finset.sum_add_distrib]

/-- Scalar multiplication commutes with the fixed-degree lift. -/
theorem diskLift_smul (n : ℕ) (a : R) (p : Polynomial R) :
    diskLift n (a • p) = a • diskLift n p := by
  simp only [diskLift, Polynomial.coeff_smul, smul_eq_mul, map_mul,
    MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Evaluation of a univariate polynomial embedded in one coordinate. -/
theorem eval_eval₂_C_X {R σ : Type*} [CommRing R]
    (p : Polynomial R) (v : σ → R) (i : σ) :
    eval v (p.eval₂ C (X i)) = p.eval (v i) := by
  have hc : (eval v).comp C = RingHom.id R := by ext r; simp
  rw [Polynomial.hom_eval₂, hc, eval_X]
  rfl

end MvPolynomial
