/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialEquation
import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.LinearCombination

/-! # Polynomial uniqueness for the Jacobi differential equation
At a nonsingular endpoint, the value at one determines a polynomial solution.
Reference: DLMF Table 18.8.1.
-/
public section
namespace Polynomial

/-- A polynomial solution vanishing at one is zero when the endpoint coefficients
are nonzero (DLMF Table 18.8.1). -/
theorem eq_zero_of_jacobi_ode {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [Algebra ℚ R]
    (α β γ : R) (p : R[X])
    (hα : ∀ k : ℕ, α + k + 1 ≠ 0)
    (he : (1 - X ^ 2) * derivative (derivative p) +
      (C (β - α) - C (α + β + 2) * X) * derivative p + C γ * p = 0)
    (hv : p.eval 1 = 0) : p = 0 := by
  let : HasUniqueDiv R := HasUniqueDiv.of_module_rat R
  induction hn : p.natDegree using Nat.strong_induction_on generalizing α β γ p with
  | h n ih =>
    have hdv : (derivative p).eval 1 = 0 := by
      have h := congrArg (fun q : R[X] ↦ q.eval 1) he
      simp only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X,
        one_pow, sub_self, zero_mul, zero_add, eval_C, eval_zero, mul_one, hv, mul_zero, add_zero] at h
      have hz : (-2 * (α + 1)) * (derivative p).eval 1 = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) (by simpa using hα 0))
    have hd : derivative p = 0 := by
      by_cases hp : p.natDegree = 0
      · exact derivative_of_natDegree_zero hp
      have he' := congrArg derivative he
      simp only [derivative_add, derivative_mul, derivative_sub, derivative_one,
        derivative_X_pow, Nat.cast_ofNat, Nat.reduceSub, pow_one, derivative_X, derivative_C, zero_mul, zero_sub,
        zero_add, mul_one, derivative_zero] at he'
      apply ih (derivative p).natDegree (by rw [← hn]; exact natDegree_derivative_lt hp)
        (α + 1) (β + 1) (γ - (α + β + 2)) (derivative p)
      · intro k
        convert hα (k + 1) using 1
        push_cast
        ring
      · simp only [map_add, map_sub, map_ofNat, map_one]
        simp only [map_add, map_sub, map_ofNat] at he'
        linear_combination he'
      · exact hdv
      · rfl
    have hc := eq_C_of_derivative_eq_zero hd
    have heval := congrArg (fun q : R[X] ↦ q.eval 1) hc
    simp only [eval_C, hv] at heval
    rw [hc, ← heval, C_0]

end Polynomial
