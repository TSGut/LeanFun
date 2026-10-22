/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Map
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.ODEUniqueness
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Chebyshev--Jacobi bridges
The existing integer-indexed Chebyshev polynomials are used unchanged.
References: DLMF 18.7.3--4.
-/
public section
namespace Polynomial

private theorem jacobi_eq_T_rat (n : ℕ) :
    jacobi (-1 / 2 : ℚ) (-1 / 2) n =
      C ((jacobi (-1 / 2 : ℚ) (-1 / 2) n).eval 1) * Chebyshev.T ℚ n := by
  apply sub_eq_zero.mp
  apply eq_zero_of_jacobi_ode (-1 / 2) (-1 / 2) ((n : ℚ) ^ 2) _
    (fun k ↦ ne_of_gt (by have hk := Nat.cast_nonneg (α := ℚ) k; linarith))
  · have hj := jacobi_differentialEquation (-1 / 2 : ℚ) (-1 / 2) n
    have ht := Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℚ) n
    have hc : (n : ℚ) + (-1 / 2) + (-1 / 2) + 1 = n := by ring
    rw [hc] at hj
    norm_num only [derivative_sub, derivative_C_mul, derivative_mul, derivative_add,
      derivative_C, derivative_zero, derivative_natCast, derivative_ofNat, derivative_one,
      zero_mul, zero_add, mul_one, sub_self, C_0, zero_sub,
      map_one, map_pow, map_natCast] at hj ⊢
    norm_num only [Function.iterate_succ_apply, Function.iterate_zero_apply,
      Int.cast_natCast] at ht
    linear_combination (norm := (simp only [neg_div, map_mul, map_natCast]; ring_nf))
      hj - C ((jacobi (-1 / 2 : ℚ) (-1 / 2) n).eval 1) * ht
  · simp [Chebyshev.T_eval_one]

private theorem jacobi_eq_U_rat (n : ℕ) :
    C (n + 1 : ℚ) * jacobi (1 / 2 : ℚ) (1 / 2) n =
      C ((jacobi (1 / 2 : ℚ) (1 / 2) n).eval 1) * Chebyshev.U ℚ n := by
  apply sub_eq_zero.mp
  apply eq_zero_of_jacobi_ode (1 / 2) (1 / 2) ((n : ℚ) * (n + 2)) _
    (fun k ↦ ne_of_gt (by have hk := Nat.cast_nonneg (α := ℚ) k; linarith))
  · have hj := jacobi_differentialEquation (1 / 2 : ℚ) (1 / 2) n
    have ht := Chebyshev.one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (R := ℚ) n
    have hc : (n : ℚ) + (1 / 2) + (1 / 2) + 1 = n + 2 := by ring
    rw [hc] at hj
    norm_num only [derivative_sub, derivative_C_mul, derivative_mul, derivative_add,
      derivative_C, derivative_zero, derivative_natCast, derivative_ofNat, derivative_one,
      zero_mul, zero_add, mul_one, sub_self, C_0, zero_sub,
      map_one, map_pow, map_natCast, map_mul, map_add, map_ofNat] at hj ⊢
    norm_num only [Function.iterate_succ_apply, Function.iterate_zero_apply,
      Int.cast_natCast, Int.cast_add, Int.cast_ofNat] at ht
    linear_combination (norm := (simp only [map_add, map_natCast, map_one]; ring_nf))
      C (n + 1 : ℚ) * hj - C ((jacobi (1 / 2 : ℚ) (1 / 2) n).eval 1) * ht
  · simp [Chebyshev.U_eval_one, mul_comm]

/-- The first-kind Chebyshev bridge with its exact normalisation (DLMF 18.7.3). -/
theorem jacobi_eq_chebyshev_T (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    jacobi (algebraMap ℚ R (-1 / 2)) (algebraMap ℚ R (-1 / 2)) n =
      C (algebraMap ℚ R ((n.factorial : ℚ)⁻¹) *
        (ascPochhammer R n).eval (algebraMap ℚ R (1 / 2))) * Chebyshev.T R n := by
  let f : ℚ →ₐ[ℚ] R := Algebra.ofId ℚ R
  have h := congrArg (Polynomial.map f.toRingHom) (jacobi_eq_T_rat n)
  have hp (x : ℚ) : f ((ascPochhammer ℚ n).eval x) = (ascPochhammer R n).eval (f x) := by
    rw [← ascPochhammer_map f.toRingHom, eval_map]
    exact (eval₂_at_apply f.toRingHom x).symm
  simp only [Polynomial.map_mul, Polynomial.map_C, map_jacobi, Chebyshev.map_T] at h
  simp only [eval_jacobi_one] at h
  norm_num at h
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, hp, f,
    Algebra.ofId_apply, neg_div, map_neg] using h

/-- The second-kind Chebyshev bridge with its exact normalisation (DLMF 18.7.4). -/
theorem jacobi_eq_chebyshev_U (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    C (n + 1 : R) * jacobi (algebraMap ℚ R (1 / 2)) (algebraMap ℚ R (1 / 2)) n =
      C (algebraMap ℚ R ((n.factorial : ℚ)⁻¹) *
        (ascPochhammer R n).eval (algebraMap ℚ R (3 / 2))) * Chebyshev.U R n := by
  let f : ℚ →ₐ[ℚ] R := Algebra.ofId ℚ R
  have h := congrArg (Polynomial.map f.toRingHom) (jacobi_eq_U_rat n)
  have hp (x : ℚ) : f ((ascPochhammer ℚ n).eval x) = (ascPochhammer R n).eval (f x) := by
    rw [← ascPochhammer_map f.toRingHom, eval_map]
    exact (eval₂_at_apply f.toRingHom x).symm
  simp only [Polynomial.map_mul, Polynomial.map_C, map_jacobi, Chebyshev.map_U] at h
  simp only [eval_jacobi_one] at h
  norm_num at h
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, hp,
    map_add, map_natCast, map_one, f, Algebra.ofId_apply] using h

end Polynomial
