/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Symmetry
public import LeanFun.Mathlib.RingTheory.Polynomial.Reflection
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Coefficient parity of symmetric Jacobi polynomials

Symmetric Jacobi polynomials have the parity of their degree. The coefficient
form is useful for polynomial constructions on disks without square-root denominators.
Reference: DLMF Table 18.6.1; Dunkl–Xu, *Orthogonal Polynomials of Several Variables*.
-/

public section
namespace Polynomial

/-- Symmetric real Jacobi coefficients of the wrong parity vanish, including
parameter values where the polynomial degenerates. -/
theorem coeff_jacobi_symmetric_eq_zero_of_parity (β : ℝ) (n j : ℕ)
    (h : j % 2 ≠ n % 2) : (jacobi β β n).coeff j = 0 := by
  have he := congrArg (fun p : ℝ[X] => p.coeff j) (jacobi_comp_neg_X β β n)
  rw [coeff_comp_neg_X, coeff_C_mul] at he
  rw [neg_one_pow_eq_pow_mod_two j, neg_one_pow_eq_pow_mod_two n] at he
  have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hn : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hc : (j % 2 = 0 ∧ n % 2 = 1) ∨ (j % 2 = 1 ∧ n % 2 = 0) := by omega
  rcases hc with ⟨hj, hn⟩ | ⟨hj, hn⟩ <;>
    rw [hj, hn] at he <;> simp only [pow_zero, pow_one, one_mul, neg_one_mul] at he <;>
    linarith

end Polynomial
