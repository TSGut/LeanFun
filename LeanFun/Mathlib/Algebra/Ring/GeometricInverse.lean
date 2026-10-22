/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.Ring.GeomSum

/-!
# A finite inverse expansion with exact remainder

No infinite series or convergence assumption is needed. Applied to a finite
matrix perturbation, this isolates its first possible elimination-path term.
Reference: the finite geometric-sum identity.
-/

public section

/-- A right inverse of `1-x` has a finite geometric expansion with an exact remainder. -/
theorem eq_geom_sum_add_pow_mul_of_one_sub_mul_eq_one {R : Type*} [Ring R]
    (x y : R) (hy : (1-x)*y=1) (n : ℕ) :
    y = (∑ k ∈ Finset.range n, x^k) + x^n*y := by
  have h := congrArg (fun z : R => z*y) (geom_sum_mul_neg x n)
  rw [mul_assoc, hy, mul_one, sub_mul, one_mul] at h
  exact (eq_sub_iff_add_eq.mp h).symm
