/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Map
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Recurrence
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Recurrence
import Mathlib.Tactic.LinearCombination

/-! # Gegenbauer endpoint normalisation
Reference: DLMF Table 18.6.1.
-/
public section
namespace Polynomial
private theorem eval_gegenbauer_one_domain {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [Algebra ℚ R] (lam : R) (n : ℕ) :
    (gegenbauer lam n).eval 1 = (jacobi (2 * lam - 1) 0 n).eval 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [eval_jacobi_one]
  | more n ih0 ih1 =>
    have he := congrArg (fun p : R[X] ↦ p.eval 1) (gegenbauer_recurrence lam n)
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, mul_one, eval_zero, ih0, ih1] at he
    have h0 := succ_mul_eval_jacobi_one (2 * lam - 1) (0 : R) n
    have h1 := succ_mul_eval_jacobi_one (2 * lam - 1) (0 : R) (n + 1)
    apply mul_left_cancel₀ (show (n + 1 : R) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
    apply mul_left_cancel₀ (show (n + 2 : R) ≠ 0 by exact_mod_cast (by omega : n + 2 ≠ 0))
    push_cast at h1
    linear_combination (n + 1 : R) * he - (n + 1 : R) * h1 + (n + 1 : R) * h0

/-- The Gegenbauer value at one, including exceptional parameters (DLMF Table 18.6.1). -/
theorem eval_gegenbauer_one {R : Type*} [CommRing R] [Algebra ℚ R]
    (lam : R) (n : ℕ) :
    (gegenbauer lam n).eval 1 = algebraMap ℚ R ((n.factorial : ℚ)⁻¹) *
      (ascPochhammer R n).eval (2 * lam) := by
  have h := eval_gegenbauer_one_domain (X : ℚ[X]) n
  let f : ℚ[X] →ₐ[ℚ] R := aeval lam
  have hm := congrArg f h
  have hg := map_gegenbauer f X n
  have hj := map_jacobi f (2 * X - 1) 0 n
  have hev (p : ℚ[X][X]) : f (p.eval 1) = (p.map f.toRingHom).eval 1 := by
    rw [eval_map, eval₂_at_one]; rfl
  rw [hev, hev, hg, hj] at hm
  simpa [f, eval_jacobi_one, map_ofNat] using hm

end Polynomial
