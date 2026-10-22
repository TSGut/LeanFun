/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Map
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialEquation
import Mathlib.Tactic.LinearCombination

/-! # Jacobi symmetry
Reflection exchanges the two parameters (DLMF Table 18.6.1).
-/
public section
namespace Polynomial

private theorem jacobi_comp_neg_X_of_nonzero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [Algebra ℚ R] (α β : R) (n : ℕ)
    (h : ∀ k : ℕ, (k : R) + α + β + 1 ≠ 0) :
    (jacobi α β n).comp (-X) = C ((-1 : R) ^ n) * jacobi β α n := by
  induction n generalizing α β with
  | zero => simp
  | succ n ih =>
    let p := (jacobi α β (n + 1)).comp (-X)
    let q := C ((-1 : R) ^ (n + 1)) * jacobi β α (n + 1)
    have hi := ih (α + 1) (β + 1) (fun k ↦ by
      convert h (k + 2) using 1
      push_cast
      ring)
    have hd : derivative (p - q) = 0 := by
      dsimp only [p, q]
      simp only [derivative_sub, derivative_comp, derivative_neg, derivative_X,
        derivative_C_mul, derivative_jacobi_succ, mul_comp, C_comp]
      rw [hi]
      simp only [pow_succ, map_mul, map_add, map_natCast, map_ofNat, map_one, map_neg]
      ring
    have hd' : derivative p = derivative q := sub_eq_zero.mp (by simpa using hd)
    have he := congrArg (fun t : R[X] ↦ t.comp (-X))
      (jacobi_differentialEquation α β (n + 1))
    have heq := jacobi_differentialEquation β α (n + 1)
    have he' : (1 - X ^ 2) * derivative (derivative p) +
        (C (α - β) - C (β + α + 2) * X) * derivative p +
        C (((n + 1 : ℕ) : R) * (((n + 1 : ℕ) : R) + α + β + 1)) * p = 0 := by
      dsimp only [p]
      simp only [derivative_comp, derivative_neg, derivative_X, derivative_mul,
        derivative_neg, derivative_one, neg_mul,
        zero_mul]
      simp only [add_comp, mul_comp, sub_comp, one_comp, pow_comp, X_comp, C_comp,
        zero_comp] at he
      simp only [map_add, map_sub, map_ofNat] at he ⊢
      linear_combination he
    have her : C (((n + 1 : ℕ) : R) * (((n + 1 : ℕ) : R) + α + β + 1)) * (p - q) = 0 := by
      rw [hd'] at he'
      dsimp only [q] at he' ⊢
      simp only [derivative_C_mul, map_add, map_sub, map_mul, map_natCast,
        map_ofNat, map_one] at he' heq ⊢
      linear_combination he' - C ((-1 : R) ^ (n + 1)) * heq
    exact sub_eq_zero.mp ((mul_eq_zero.mp her).resolve_left (by
      apply C_ne_zero.mpr
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (h (n + 1))))

/-- Reflection swaps the Jacobi parameters, including degenerate specialisations
(DLMF Table 18.6.1). -/
theorem jacobi_comp_neg_X {R : Type*} [CommRing R] [Algebra ℚ R]
    (α β : R) (n : ℕ) :
    (jacobi α β n).comp (-X) = C ((-1 : R) ^ n) * jacobi β α n := by
  have h := jacobi_comp_neg_X_of_nonzero (X : ℚ[X][X]) (C X) n (fun k hk ↦ by
    have hc := congrArg (fun p : ℚ[X][X] ↦ p.coeff 1) hk
    have hk : (k : ℚ[X][X]) = C (k : ℚ[X]) := by simp
    rw [hk] at hc
    norm_num [coeff_add, coeff_one] at hc)
  let f : ℚ[X][X] →ₐ[ℚ] R := eval₂AlgHom (aeval β) α (fun _ ↦ Commute.all _ _)
  have hm := congrArg (Polynomial.map f.toRingHom) h
  simp only [map_comp, Polynomial.map_neg, map_X, Polynomial.map_mul,
    Polynomial.map_C, map_jacobi] at hm
  simpa [f, eval₂_pow, eval₂_neg, eval₂_one] using hm


/-- Evaluation form of Jacobi reflection (DLMF Table 18.6.1). -/
theorem eval_jacobi_neg {R : Type*} [CommRing R] [Algebra ℚ R]
    (α β x : R) (n : ℕ) :
    (jacobi α β n).eval (-x) = (-1 : R) ^ n * (jacobi β α n).eval x := by
  have h := congrArg (fun p : R[X] ↦ p.eval x) (jacobi_comp_neg_X α β n)
  simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] using h

/-- The other endpoint normalisation (DLMF Table 18.6.1). -/
theorem eval_jacobi_neg_one {R : Type*} [CommRing R] [Algebra ℚ R]
    (α β : R) (n : ℕ) :
    (jacobi α β n).eval (-1) = (-1 : R) ^ n *
      (algebraMap ℚ R ((n.factorial : ℚ)⁻¹) * (ascPochhammer R n).eval (β + 1)) := by
  rw [eval_jacobi_neg, eval_jacobi_one]

end Polynomial
