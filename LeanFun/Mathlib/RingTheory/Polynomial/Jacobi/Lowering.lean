/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Symmetry
import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.LinearCombination

/-! # A Jacobi differential lowering identity
The cleared identity includes exceptional parameters. Its shifted `(0,1)`
specialization supplies the Volterra antiderivative in the `(1,0)` basis.
Derived from DLMF 18.9.15 and endpoint symmetry; Volterra application:
Gutleb–Olver, arXiv:1906.03907, Section 3.1.
-/

public section
namespace Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Lowering the second parameter by a first-order differential operator. -/
theorem jacobi_lower_beta (α β : R) (n : ℕ) :
    (X+1) * derivative (jacobi α β n) + C β * jacobi α β n =
      C ((n : R)+β) * jacobi (α+1) (β-1) n := by
  let : HasUniqueDiv R := HasUniqueDiv.of_module_rat R
  let r (α β : R) (n : ℕ) :=
    (X+1) * derivative (jacobi α β n) + C β * jacobi α β n -
      C ((n : R)+β) * jacobi (α+1) (β-1) n
  have hz (α β : R) (n : ℕ) : (r α β n).eval (-1) = 0 := by
    have hp := congrArg (fun p : R[X] ↦ p.eval β)
      ((ascPochhammer_succ_left R n).symm.trans (ascPochhammer_succ_right R n))
    simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one,
      eval_natCast] at hp
    dsimp [r]
    simp only [eval_sub, eval_add, eval_mul, eval_X, eval_one, eval_C,
      neg_add_cancel, zero_mul, zero_add, eval_jacobi_neg_one]
    simp only [sub_add_cancel]
    linear_combination ((-1 : R)^n * algebraMap ℚ R ((n.factorial : ℚ)⁻¹)) * hp
  have hr : ∀ n : ℕ, ∀ α β : R, r α β n = 0 := by
    intro n
    induction n with
    | zero => intro α β; simp [r]
    | succ n ih =>
      intro α β
      have hd : derivative (r α β (n+1)) = 0 := by
        have hi := ih (α+1) (β+1)
        dsimp only [r] at hi ⊢
        simp only [derivative_sub, derivative_add, derivative_mul, derivative_X,
          derivative_one, add_zero, one_mul, derivative_C, zero_mul, zero_add,
          derivative_jacobi_succ]
        simp only [show β-1+1=β by ring, show β+1-1=β by ring] at *
        simp only [Nat.cast_add, Nat.cast_one, map_add, map_sub, map_mul,
          map_natCast, map_one, map_ofNat] at hi ⊢
        linear_combination (C (algebraMap ℚ R (1/2)) * ((n : R[X])+C α+C β+2)) * hi
      have hc := eq_C_of_derivative_eq_zero hd
      have he := congrArg (fun p : R[X] ↦ p.eval (-1)) hc
      rw [hz, eval_C] at he
      rw [hc, ← he, C_0]
  exact sub_eq_zero.mp (hr n α β)

end Polynomial
