/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Algebra.Algebra.Factorial
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Map
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.ODEUniqueness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # The cleared Jacobi recurrence
The three-term identity includes degenerate parameters (DLMF 18.9.1--2).
-/
public section
namespace Polynomial

/-- Successive endpoint values satisfy a cleared rising-factorial relation
(DLMF Table 18.6.1). -/
theorem succ_mul_eval_jacobi_one {R : Type*} [CommRing R] [Algebra ℚ R]
    (α β : R) (n : ℕ) :
    (n + 1 : R) * (jacobi α β (n + 1)).eval 1 =
      (n + α + 1) * (jacobi α β n).eval 1 := by
  rw [eval_jacobi_one, eval_jacobi_one, ascPochhammer_succ_eval]
  have hf : (n + 1 : R) * algebraMap ℚ R (((n + 1).factorial : ℚ)⁻¹) =
      algebraMap ℚ R ((n.factorial : ℚ)⁻¹) :=
    Nat.cast_succ_mul_algebraMap_inv_factorial R n
  linear_combination (ascPochhammer R n).eval (α + 1) * (α + 1 + n) * hf

private theorem jacobi_raise_of_nonzero {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [Algebra ℚ R] (α β : R) (n : ℕ)
    (hα : ∀ k : ℕ, α + k + 1 ≠ 0) :
    C (2 * n + α + β + 2) * (1 - X ^ 2) * derivative (jacobi α β n) -
      C (n + α + β + 1) * (C (α - β) + C (2 * n + α + β + 2) * X) * jacobi α β n +
      C (2 * (n + 1) * (n + α + β + 1)) * jacobi α β (n + 1) = 0 := by
  apply eq_zero_of_jacobi_ode α β ((n + 1) * (n + α + β + 2)) _ hα
  · have he := jacobi_differentialEquation α β n
    have hed := congrArg derivative he
    have heq := jacobi_differentialEquation α β (n + 1)
    simp only [derivative_add, derivative_sub, derivative_neg, derivative_mul, derivative_C,
      derivative_one, derivative_X_pow, derivative_X, derivative_zero,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, mul_zero, zero_add,
      add_zero, zero_sub, mul_one] at hed ⊢
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_sub, map_mul, map_natCast,
      map_ofNat, map_one] at he hed heq ⊢
    linear_combination (norm :=
      (simp only [map_add, map_sub, map_mul, map_natCast, map_ofNat, map_one]; ring_nf))
      C (2 * n + α + β + 2) * (1 - X ^ 2) * hed +
      (-(C (n + α + β + 3) * C (2 * n + α + β + 2) * X) -
        C (n + α + β + 1) * C (α - β)) * he +
      C (2 * (n + 1) * (n + α + β + 1)) * heq
  · simp only [eval_add, eval_sub, eval_mul, eval_C, eval_one, eval_pow, eval_X,
      one_pow, sub_self, mul_zero, zero_mul, zero_sub, mul_one]
    have h := succ_mul_eval_jacobi_one α β n
    linear_combination 2 * (n + α + β + 1) * h

private theorem jacobi_lower_of_nonzero {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [Algebra ℚ R] (α β : R) (n : ℕ)
    (hα : ∀ k : ℕ, α + k + 1 ≠ 0) :
    C (2 * n + α + β + 2) * (1 - X ^ 2) * derivative (jacobi α β (n + 1)) -
      C (n + 1 : R) * (C (α - β) - C (2 * n + α + β + 2) * X) * jacobi α β (n + 1) -
      C (2 * (n + α + 1) * (n + β + 1)) * jacobi α β n = 0 := by
  apply eq_zero_of_jacobi_ode α β (n * (n + α + β + 1)) _ hα
  · have he := jacobi_differentialEquation α β (n + 1)
    have hed := congrArg derivative he
    have heq := jacobi_differentialEquation α β n
    simp only [derivative_add, derivative_sub, derivative_neg, derivative_mul, derivative_C,
      derivative_one, derivative_X_pow, derivative_X, derivative_zero,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, zero_add,
      zero_sub, mul_one] at hed ⊢
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_sub, map_mul, map_natCast,
      map_ofNat, map_one] at he hed heq ⊢
    linear_combination (norm :=
      (simp only [map_add, map_sub, map_mul, map_natCast, map_ofNat, map_one]; ring_nf))
      C (2 * n + α + β + 2) * (1 - X ^ 2) * hed +
      (C ((n : R) - 1) * C (2 * n + α + β + 2) * X -
        C (n + 1 : R) * C (α - β)) * he -
      C (2 * (n + α + 1) * (n + β + 1)) * heq
  · simp only [eval_sub, eval_mul, eval_C, eval_one, eval_pow, eval_X,
      one_pow, sub_self, mul_zero, zero_mul, zero_sub, mul_one]
    have h := succ_mul_eval_jacobi_one α β n
    linear_combination 2 * (n + β + 1) * h

private theorem jacobi_recurrence_of_nonzero {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [Algebra ℚ R] (α β : R) (n : ℕ)
    (hα : ∀ k : ℕ, α + k + 1 ≠ 0) :
    C (2 * (n + 2) * (n + α + β + 2) * (2 * n + α + β + 2)) * jacobi α β (n + 2) =
      C (2 * n + α + β + 3) *
        (C ((2 * n + α + β + 2) * (2 * n + α + β + 4)) * X + C (α ^ 2 - β ^ 2)) *
        jacobi α β (n + 1) -
      C (2 * (n + α + 1) * (n + β + 1) * (2 * n + α + β + 4)) * jacobi α β n := by
  have hu := jacobi_raise_of_nonzero α β (n + 1) hα
  have hl := jacobi_lower_of_nonzero α β n hα
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_sub, map_mul, map_natCast,
    map_ofNat, map_one, map_pow] at hu hl ⊢
  linear_combination (norm := (simp only [map_add, map_mul, map_natCast, map_ofNat]; ring_nf))
    C (2 * n + α + β + 2) * hu - C (2 * n + α + β + 4) * hl

/-- The three-term Jacobi recurrence with all parameter denominators cleared,
valid over every commutative rational algebra (DLMF 18.9.1--2, index shifted by one). -/
theorem jacobi_recurrence {R : Type*} [CommRing R] [Algebra ℚ R]
    (α β : R) (n : ℕ) :
    C (2 * (n + 2) * (n + α + β + 2) * (2 * n + α + β + 2)) * jacobi α β (n + 2) =
      C (2 * n + α + β + 3) *
        (C ((2 * n + α + β + 2) * (2 * n + α + β + 4)) * X + C (α ^ 2 - β ^ 2)) *
        jacobi α β (n + 1) -
      C (2 * (n + α + 1) * (n + β + 1) * (2 * n + α + β + 4)) * jacobi α β n := by
  have h := jacobi_recurrence_of_nonzero (X : ℚ[X][X]) (C X) n (fun k hk ↦ by
    have hc := congrArg (fun p : ℚ[X][X] ↦ p.coeff 1) hk
    norm_num [coeff_add, coeff_natCast_ite, coeff_one] at hc)
  let f : ℚ[X][X] →ₐ[ℚ] R := eval₂AlgHom (aeval β) α (fun _ ↦ Commute.all _ _)
  have hm := congrArg (Polynomial.map f.toRingHom) h
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_C, map_X, map_jacobi] at hm
  simpa [f, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_natCast, eval₂_ofNat] using hm

/-- The cleared first-order lowering identity, including degenerate parameters.
This derivative form complements the three-term recurrence (DLMF 18.9). -/
theorem jacobi_derivative_lowering {R : Type*} [CommRing R] [Algebra ℚ R]
    (α β : R) (n : ℕ) :
    C (2 * n + α + β + 2) * (1 - X ^ 2) * derivative (jacobi α β (n + 1)) -
      C (n + 1 : R) * (C (α - β) - C (2 * n + α + β + 2) * X) * jacobi α β (n + 1) -
      C (2 * (n + α + 1) * (n + β + 1)) * jacobi α β n = 0 := by
  have h := jacobi_lower_of_nonzero (X : ℚ[X][X]) (C X) n (fun k hk ↦ by
    have hc := congrArg (fun p : ℚ[X][X] ↦ p.coeff 1) hk
    norm_num [coeff_add, coeff_natCast_ite, coeff_one] at hc)
  let f : ℚ[X][X] →ₐ[ℚ] R := eval₂AlgHom (aeval β) α (fun _ ↦ Commute.all _ _)
  have hm := congrArg (Polynomial.map f.toRingHom) h
  simp only [Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_zero,
    Polynomial.map_C, map_X, ← derivative_map, map_jacobi] at hm
  simpa [f, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_natCast, eval₂_ofNat] using hm

end Polynomial
