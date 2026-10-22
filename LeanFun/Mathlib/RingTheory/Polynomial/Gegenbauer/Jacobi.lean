/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Endpoint
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.DifferentialEquation
import Mathlib.Tactic.LinearCombination

/-! # The universal Gegenbauer--Jacobi bridge
The factor depending on the parameter is kept on the left, so singular
specialisations remain valid (DLMF 18.7.1).
-/
public section
namespace Polynomial
private theorem gegenbauer_jacobi_of_nonzero {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [Algebra ℚ R] (lam : R) (n : ℕ)
    (h : ∀ k : ℕ, lam - algebraMap ℚ R (1 / 2) + k + 1 ≠ 0) :
    C ((ascPochhammer R n).eval (lam + algebraMap ℚ R (1 / 2))) * gegenbauer lam n =
      C ((ascPochhammer R n).eval (2 * lam)) *
        jacobi (lam - algebraMap ℚ R (1 / 2)) (lam - algebraMap ℚ R (1 / 2)) n := by
  let a := lam - algebraMap ℚ R (1 / 2)
  have hh : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
    have h := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  have hab : a + a + 2 = 2 * lam + 1 := by dsimp [a]; linear_combination -hh
  have han : (n : R) + a + a + 1 = n + 2 * lam := by dsimp [a]; linear_combination -hh
  have ha1 : a + 1 = lam + algebraMap ℚ R (1 / 2) := by dsimp [a]; linear_combination -hh
  apply sub_eq_zero.mp
  apply eq_zero_of_jacobi_ode a a (n * (n + 2 * lam)) _ h
  · have hg := gegenbauer_differentialEquation lam n
    have hj := jacobi_differentialEquation a a n
    rw [hab, han] at hj
    rw [hab]
    simp only [sub_self, C_0, zero_sub, derivative_sub, derivative_C_mul] at hj ⊢
    linear_combination C ((ascPochhammer R n).eval (lam + algebraMap ℚ R (1 / 2))) * hg -
      C ((ascPochhammer R n).eval (2 * lam)) * hj
  · change (C _ * gegenbauer lam n - C _ * jacobi a a n).eval 1 = 0
    rw [eval_sub, eval_mul, eval_mul, eval_C, eval_C, eval_gegenbauer_one, eval_jacobi_one, ha1]
    ring

/-- The cleared Gegenbauer--Jacobi bridge at every parameter (DLMF 18.7.1). -/
theorem gegenbauer_jacobi {R : Type*} [CommRing R] [Algebra ℚ R]
    (lam : R) (n : ℕ) :
    C ((ascPochhammer R n).eval (lam + algebraMap ℚ R (1 / 2))) * gegenbauer lam n =
      C ((ascPochhammer R n).eval (2 * lam)) *
        jacobi (lam - algebraMap ℚ R (1 / 2)) (lam - algebraMap ℚ R (1 / 2)) n := by
  have h := gegenbauer_jacobi_of_nonzero (X : ℚ[X]) n (fun k hk ↦ by
    have hc := congrArg (fun p : ℚ[X] ↦ p.coeff 1) hk
    norm_num [coeff_add, coeff_sub, coeff_natCast_ite, coeff_one, algebraMap_apply] at hc)
  let f : ℚ[X] →ₐ[ℚ] R := aeval lam
  have hp (k : ℕ) (x : ℚ[X]) : f ((ascPochhammer ℚ[X] k).eval x) =
      (ascPochhammer R k).eval (f x) := by
    rw [← ascPochhammer_map f.toRingHom, eval_map]
    exact (eval₂_at_apply f.toRingHom x).symm
  have hm := congrArg (Polynomial.map f.toRingHom) h
  simp only [Polynomial.map_mul, Polynomial.map_C, map_gegenbauer, map_jacobi] at hm
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hp, map_add, map_sub,
    map_mul, map_ofNat, AlgHom.commutes] at hm
  simpa [f] using hm

end Polynomial
