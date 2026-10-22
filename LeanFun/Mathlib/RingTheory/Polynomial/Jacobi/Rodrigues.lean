/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialEquation
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Map
import Mathlib.Tactic.LinearCombination

/-!
# Algebraic Jacobi Rodrigues identities

The first-order identity underlying Rodrigues' formula is polynomial in the
parameters, so exceptional parameters are included. Reference: DLMF 18.5.5.
-/

public section
namespace Polynomial

private theorem jacobi_rodrigues_step_of_ne_zero {R : Type*} [CommRing R]
    [IsDomain R] [Algebra ℚ R] (α β : R) (n : ℕ)
    (h : (n : R) + α + β + 2 ≠ 0) :
    (1 - X ^ 2) * derivative (jacobi (α + 1) (β + 1) n) +
      (C (β - α) - C (α + β + 2) * X) * jacobi (α + 1) (β + 1) n =
      -C (2 * (n + 1 : R)) * jacobi α β (n + 1) := by
  have he := jacobi_differentialEquation α β (n + 1)
  rw [derivative_jacobi_succ, derivative_C_mul] at he
  have hh : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
    have hm := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using hm
  apply mul_left_cancel₀ (show C ((n : R) + α + β + 2) ≠ 0 from C_ne_zero.mpr h)
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_sub, map_mul, map_natCast,
    map_ofNat, map_one] at he ⊢
  have hh' := congrArg (C : R →+* R[X]) hh
  simp only [map_mul, map_ofNat, map_one] at hh'
  linear_combination (norm :=
    (simp only [map_add, map_sub, map_natCast, map_ofNat]; ring_nf)) 2 * he -
    ((1 - X ^ 2) * derivative (jacobi (α + 1) (β + 1) n) +
      (C (β - α) - C (α + β + 2) * X) * jacobi (α + 1) (β + 1) n) *
      C ((n : R) + α + β + 2) * hh'

/-- The polynomial first-order identity underlying Jacobi Rodrigues' formula,
with no parameter restrictions (DLMF 18.5.5 and 18.9.16). -/
theorem jacobi_rodrigues_step {R : Type*} [CommRing R] [Algebra ℚ R]
    (α β : R) (n : ℕ) :
    (1 - X ^ 2) * derivative (jacobi (α + 1) (β + 1) n) +
      (C (β - α) - C (α + β + 2) * X) * jacobi (α + 1) (β + 1) n =
      -C (2 * (n + 1 : R)) * jacobi α β (n + 1) := by
  have h := jacobi_rodrigues_step_of_ne_zero (X : ℚ[X][X]) (C X) n (by
    intro hz
    have hc := congrArg (fun p : ℚ[X][X] ↦ p.coeff 1) hz
    norm_num [coeff_add, coeff_natCast_ite] at hc)
  let f : ℚ[X][X] →ₐ[ℚ] R := eval₂AlgHom (aeval β) α (fun _ ↦ Commute.all _ _)
  have hm := congrArg (Polynomial.map f.toRingHom) h
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_neg, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_C,
    map_X, ← derivative_map, map_jacobi] at hm
  simpa [f, eval₂_add, eval₂_sub, eval₂_mul, eval₂_natCast, eval₂_ofNat] using hm

end Polynomial
