/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Recurrence
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Map
public import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.LinearCombination

/-! # Entry from Chebyshev to ultraspherical polynomials
The parameter-one Gegenbauer family is exactly Chebyshev U. Chebyshev T enters
the ladder by a two-diagonal conversion and by differentiation.
References: DLMF 18.7.4, 18.9.19; Olver–Townsend (2013), Section 2.
-/

public section
namespace Polynomial

private theorem gegenbauer_one_eq_U_rat (n : ℕ) :
    gegenbauer (1 : ℚ) n = Chebyshev.U ℚ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [gegenbauer_one, map_ofNat]
  | more n h₀ h₁ =>
    have hr := gegenbauer_recurrence (1 : ℚ) n
    rw [h₀, h₁] at hr
    apply mul_left_cancel₀ (a := C (n + 2 : ℚ)) (C_ne_zero.mpr (by positivity))
    simp only [Nat.cast_add, Nat.cast_ofNat, Chebyshev.U_add_two]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_ofNat,
      map_one, map_natCast] at hr ⊢
    linear_combination hr

/-- Parameter-one Gegenbauer polynomials are Chebyshev U, with no rescaling
(DLMF 18.7.4). -/
theorem gegenbauer_one_eq_chebyshev_U (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    gegenbauer (1 : R) n = Chebyshev.U R n := by
  let f : ℚ →ₐ[ℚ] R := Algebra.ofId ℚ R
  have h := congrArg (Polynomial.map f.toRingHom) (gegenbauer_one_eq_U_rat n)
  simpa only [map_gegenbauer, map_one, Chebyshev.map_U] using h

/-- The positive-degree conversion from T to the first ultraspherical family,
with the factor two cleared (Olver–Townsend, equation 2.8). -/
theorem two_mul_chebyshev_T_eq_gegenbauer_sub (R : Type*) [CommRing R] [Algebra ℚ R]
    (n : ℕ) :
    2 * Chebyshev.T R (n + 2) = gegenbauer (1 : R) (n + 2) - gegenbauer (1 : R) n := by
  simp only [gegenbauer_one_eq_chebyshev_U, Nat.cast_add, Nat.cast_ofNat]
  exact Chebyshev.two_mul_T_eq_U_sub_U R n

/-- Differentiation enters the ultraspherical ladder (Olver–Townsend, equation 2.5). -/
theorem derivative_chebyshev_T_succ (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    derivative (Chebyshev.T R (n + 1)) = C (n + 1 : R) * gegenbauer (1 : R) n := by
  rw [gegenbauer_one_eq_chebyshev_U, Chebyshev.T_derivative_eq_U]
  simp

/-- Repeated differentiation has a single ultraspherical output degree
(Olver–Townsend, Section 3). The index form includes every nonzero case. -/
theorem iterate_derivative_chebyshev_T (R : Type*) [CommRing R] [Algebra ℚ R]
    (k n : ℕ) :
    derivative^[k + 1] (Chebyshev.T R (n + k + 1 : ℕ)) =
      C ((2 : R) ^ k * k.factorial * (n + k + 1)) * gegenbauer (k + 1 : R) n := by
  induction k generalizing n with
  | zero => simpa using derivative_chebyshev_T_succ R n
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [show n + (k + 1) + 1 = (n + 1) + k + 1 by omega, ih,
      derivative_C_mul, derivative_gegenbauer_succ]
    simp only [Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul,
      pow_succ, ← mul_assoc, ← map_mul]
    congr 2
    ring

/-- Differentiating beyond the degree annihilates a Chebyshev mode. -/
theorem iterate_derivative_chebyshev_T_eq_zero (R : Type*) [CommRing R] [IsDomain R]
    [NeZero (2 : R)] {n k : ℕ} (hn : n < k) :
    derivative^[k] (Chebyshev.T R n) = 0 := by
  apply iterate_derivative_eq_zero
  simpa only [Chebyshev.natDegree_T, Int.natAbs_natCast] using hn

end Polynomial
