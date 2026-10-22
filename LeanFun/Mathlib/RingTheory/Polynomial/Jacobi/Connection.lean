/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Recurrence
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Symmetry

import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.LinearCombination

/-! # Jacobi parameter raising
The conversion identities have their parameter denominators cleared, and hold
over every commutative rational algebra. Reference: DLMF 18.9.5 and its reflection.
-/

public section
namespace Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Raising the second Jacobi parameter, with denominators cleared
(DLMF 18.9.5, index shifted by one). -/
theorem jacobi_raise_beta (α β : R) (n : ℕ) :
    C (2 * n + α + β + 3) * jacobi α β (n + 1) =
      C (n + α + β + 2) * jacobi α (β + 1) (n + 1) +
        C (n + α + 1) * jacobi α (β + 1) n := by
  let : HasUniqueDiv R := HasUniqueDiv.of_module_rat R
  let r (α β : R) (n : ℕ) := C (2 * n + α + β + 3) * jacobi α β (n + 1) -
    (C (n + α + β + 2) * jacobi α (β + 1) (n + 1) +
      C (n + α + 1) * jacobi α (β + 1) n)
  have hz (α β : R) (n : ℕ) : (r α β n).eval 1 = 0 := by
    have h := succ_mul_eval_jacobi_one α β n
    dsimp only [r]
    simp only [eval_sub, eval_add, eval_mul, eval_C, eval_jacobi_one] at h ⊢
    linear_combination h
  have finish (p : R[X]) (hd : derivative p = 0) (hv : p.eval 1 = 0) : p = 0 := by
    have hc := eq_C_of_derivative_eq_zero hd
    have he := congrArg (fun q : R[X] ↦ q.eval 1) hc
    simp only [eval_C] at he
    rw [hc, he.symm.trans hv, C_0]
  have hr : ∀ n : ℕ, ∀ α β : R, r α β n = 0 := by
    intro n
    induction n with
    | zero =>
      intro α β
      apply finish _ _ (hz α β 0)
      dsimp only [r]
      simp only [derivative_sub, derivative_add, derivative_C_mul,
        derivative_jacobi_succ, jacobi_zero, derivative_one, mul_zero, add_zero]
      simp only [Nat.cast_zero, zero_add, map_zero, map_mul, map_add, map_ofNat, map_one]
      ring
    | succ n ih =>
      intro α β
      apply finish _ _ (hz α β (n + 1))
      have h := ih (α + 1) (β + 1)
      dsimp only [r] at h ⊢
      simp only [derivative_sub, derivative_add, derivative_C_mul, derivative_jacobi_succ]
      simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_natCast,
        map_ofNat, map_one] at h ⊢
      linear_combination C (algebraMap ℚ R (1 / 2)) * ((n : R[X]) + C α + C β + 3) * h
  exact sub_eq_zero.mp (hr n α β)

/-- Raising the first Jacobi parameter, with denominators cleared
(DLMF 18.9.5 reflected using Table 18.6.1). -/
theorem jacobi_raise_alpha (α β : R) (n : ℕ) :
    C (2 * n + α + β + 3) * jacobi α β (n + 1) =
      C (n + α + β + 2) * jacobi (α + 1) β (n + 1) -
        C (n + β + 1) * jacobi (α + 1) β n := by
  have h := congrArg (fun p : R[X] ↦ p.comp (-X)) (jacobi_raise_beta β α n)
  simp only [mul_comp, add_comp, C_comp, jacobi_comp_neg_X, pow_succ] at h
  have hu : IsUnit (C ((-1 : R) ^ n)) :=
    (isUnit_one.neg.pow n).map C
  apply hu.mul_left_cancel
  simp only [map_mul, map_add, map_natCast, map_ofNat, map_one, map_neg] at h ⊢
  linear_combination -h

end Polynomial
