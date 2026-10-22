/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Legendre.Jacobi
public import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Basic structure of Legendre polynomials

Degree, normalisation, polynomial sequence, derivative and differential equation.
References: DLMF Tables 18.3.1, 18.6.1, 18.8.1 and equation 18.9.15.
-/

public section

namespace Polynomial

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The constant Legendre polynomial (DLMF Table 18.3.1). -/
@[simp] theorem legendre_zero : legendre R 0 = 1 := by
  rw [legendre_eq_jacobi, jacobi_zero]

/-- The first Legendre polynomial (DLMF Table 18.3.1). -/
@[simp] theorem legendre_one : legendre R 1 = X := by
  rw [legendre_eq_jacobi, jacobi_one]
  have hh : algebraMap ℚ R (1 / 2) * (2 : R) = 1 := by
    have h := congrArg (algebraMap ℚ R) (show (1 / 2 : ℚ) * 2 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  simp only [zero_add, hh, C_1, one_mul]
  ring

/-- The endpoint normalisation of Legendre polynomials (DLMF Table 18.6.1). -/
@[simp] theorem eval_legendre_one (n : ℕ) : (legendre R n).eval 1 = 1 := by
  rw [legendre_eq_jacobi, eval_jacobi_one]
  simp only [zero_add, ascPochhammer_eval_one]
  have h := congrArg (algebraMap ℚ R)
    (inv_mul_cancel₀ (show (n.factorial : ℚ) ≠ 0 by positivity))
  simpa only [map_mul, map_natCast, map_one] using h

/-- Legendre parity at every ring element (DLMF Table 18.6.1). -/
theorem eval_legendre_neg (n : ℕ) (x : R) :
    (legendre R n).eval (-x) = (-1) ^ n * (legendre R n).eval x := by
  have h := congrArg (fun p : R[X] ↦ p.eval x) (legendre_comp_neg_X R n)
  simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] using h

/-- The value at the left endpoint (DLMF Table 18.6.1). -/
@[simp] theorem eval_legendre_neg_one (n : ℕ) : (legendre R n).eval (-1) = (-1) ^ n := by
  rw [eval_legendre_neg, eval_legendre_one, mul_one]

/-- The Legendre degree bound holds also in the trivial algebra (DLMF Table 18.3.1). -/
theorem degree_legendre_le (n : ℕ) : (legendre R n).degree ≤ n := by
  rw [legendre_eq_jacobi]
  exact degree_jacobi_le _ _ _

/-- The top coefficient is the central binomial coefficient divided by `2^n`
(DLMF Table 18.3.1). -/
theorem coeff_legendre_self (n : ℕ) :
    (legendre R n).coeff n = algebraMap ℚ R (((2 * n).choose n : ℚ) / 2 ^ n) := by
  rw [legendre_eq_jacobi, coeff_jacobi_self]
  simp only [add_zero]
  have hp : (ascPochhammer R n).eval ((n : R) + 1) =
      (n.factorial : R) * ((2 * n).choose n : R) := by
    rw [show (n : R) + 1 = ((n + 1 : ℕ) : R) by push_cast; rfl,
      ← Nat.cast_ascFactorial, Nat.ascFactorial_eq_factorial_mul_choose, ← two_mul, Nat.cast_mul]
  rw [hp]
  have h : (((n.factorial : ℚ) * 2 ^ n)⁻¹) *
      (n.factorial * ((2 * n).choose n : ℚ)) = ((2 * n).choose n : ℚ) / 2 ^ n := by
    field_simp
  simpa only [map_mul, map_natCast] using congrArg (algebraMap ℚ R) h

/-- Legendre polynomials have exact degree in every nontrivial rational algebra
(DLMF Table 18.3.1). -/
@[simp] theorem degree_legendre [Nontrivial R] (n : ℕ) : (legendre R n).degree = n := by
  apply degree_eq_of_le_of_coeff_ne_zero (degree_legendre_le R n)
  rw [coeff_legendre_self]
  rw [← map_zero (algebraMap ℚ R)]
  apply (algebraMap ℚ R).injective.ne
  have hchoose : 0 < (2 * n).choose n := Nat.choose_pos (by omega)
  positivity

/-- The natural degree of a Legendre polynomial (DLMF Table 18.3.1). -/
@[simp] theorem natDegree_legendre [Nontrivial R] (n : ℕ) :
    (legendre R n).natDegree = n := natDegree_eq_of_degree_eq_some (degree_legendre R n)

/-- The leading coefficient of a Legendre polynomial (DLMF Table 18.3.1). -/
theorem leadingCoeff_legendre [Nontrivial R] (n : ℕ) :
    (legendre R n).leadingCoeff = algebraMap ℚ R (((2 * n).choose n : ℚ) / 2 ^ n) := by
  rw [leadingCoeff, natDegree_legendre, coeff_legendre_self]

/-- The Legendre family as Mathlib's degree-indexed polynomial sequence
(DLMF Table 18.3.1). -/
@[expose] noncomputable def legendreSequence [Nontrivial R] : Polynomial.Sequence R where
  elems' := legendre R
  degree_eq' := degree_legendre R

/-- The Legendre sequence uses the Rodrigues-defined family (DLMF Table 18.3.1). -/
@[simp] theorem legendreSequence_apply [Nontrivial R] (n : ℕ) :
    legendreSequence R n = legendre R n := rfl

/-- Differentiating Legendre gives the shifted-parameter Jacobi family
(DLMF 18.9.15 at parameters zero). -/
theorem derivative_legendre_succ (n : ℕ) :
    derivative (legendre R (n + 1)) =
      C (algebraMap ℚ R (1 / 2) * ((n : R) + 2)) * jacobi (1 : R) 1 n := by
  rw [legendre_eq_jacobi, derivative_jacobi_succ]
  simp only [zero_add, add_zero]

/-- The Legendre differential equation as a polynomial identity (DLMF Table 18.8.1). -/
theorem legendre_differentialEquation (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (legendre R n)) -
      2 * X * derivative (legendre R n) + C ((n : R) * (n + 1)) * legendre R n = 0 := by
  rw [legendre_eq_jacobi]
  simpa only [sub_self, C_0, zero_add, add_zero, map_ofNat, zero_sub, neg_mul,
    sub_eq_add_neg] using jacobi_differentialEquation (0 : R) 0 n

/-- The top derivative coefficient of Legendre polynomials (DLMF Table 18.3.1). -/
theorem coeff_derivative_legendre_succ (n : ℕ) :
    (derivative (legendre R (n + 1))).coeff n = (2 * (n : R) + 1) * (legendre R n).coeff n := by
  rw [coeff_derivative, coeff_legendre_self, coeff_legendre_self]
  have h : (((2 * (n + 1)).choose (n + 1) : ℚ) / 2 ^ (n + 1)) * (n + 1) =
      (2 * (n : ℚ) + 1) * (((2 * n).choose n : ℚ) / 2 ^ n) := by
    have hc := congrArg (fun k : ℕ ↦ (k : ℚ)) (Nat.succ_mul_centralBinom_succ n)
    simp only [Nat.centralBinom, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hc
    rw [pow_succ]
    field_simp
    linear_combination hc
  have hm := congrArg (algebraMap ℚ R) h
  simpa only [map_mul, map_add, map_natCast, map_ofNat, map_one] using hm

end Polynomial
