/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer
public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Derivatives of Gegenbauer polynomials

The parameter-raising derivative identity includes parameter zero and all other
exceptional specialisations. Reference: DLMF 18.9.19.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Differentiation raises the Gegenbauer parameter by one (DLMF 18.9.19). -/
theorem derivative_gegenbauer_succ (lam : R) (n : ℕ) :
    derivative (gegenbauer lam (n + 1)) = C (2 * lam) * gegenbauer (lam + 1) n := by
  let c (lam : R) (n k : ℕ) : R := (-1) ^ k *
    algebraMap ℚ R (((k.factorial : ℚ) * (n - 2 * k).factorial)⁻¹) *
    (ascPochhammer R (n - k)).eval lam
  have hrat (k m : ℕ) :
      (m + 1 : ℚ) * (((k.factorial : ℚ) * (m + 1).factorial)⁻¹) =
      (((k.factorial : ℚ) * m.factorial)⁻¹) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  have hc (k : ℕ) (hk : k ≤ n / 2) :
      c lam (n + 1) k * ((n - 2 * k : ℕ) + 1 : R) = lam * c (lam + 1) n k := by
    have hsub : n + 1 - 2 * k = (n - 2 * k) + 1 := by omega
    have hsub' : n + 1 - k = (n - k) + 1 := by omega
    have hm := congrArg (algebraMap ℚ R) (hrat k (n - 2 * k))
    simp only [map_mul, map_add, map_natCast, map_one] at hm
    dsimp only [c]
    rw [hsub, hsub', ascPochhammer_succ_left, eval_mul, eval_X,
      eval_comp, eval_add, eval_X, eval_one]
    calc
      _ = (-1) ^ k * (((n - 2 * k : ℕ) + 1 : R) * algebraMap ℚ R
          (((k.factorial : ℚ) * ((n - 2 * k) + 1).factorial)⁻¹)) * lam *
          (ascPochhammer R (n - k)).eval (lam + 1) := by ring
      _ = _ := by rw [hm]; ring
  change derivative (∑ k ∈ Finset.range ((n + 1) / 2 + 1),
      C (c lam (n + 1) k) * (C 2 * X) ^ (n + 1 - 2 * k)) =
    C (2 * lam) * ∑ k ∈ Finset.range (n / 2 + 1),
      C (c (lam + 1) n k) * (C 2 * X) ^ (n - 2 * k)
  rw [derivative_sum]
  have hsum :
      (∑ k ∈ Finset.range ((n + 1) / 2 + 1),
        derivative (C (c lam (n + 1) k) * (C 2 * X) ^ (n + 1 - 2 * k))) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        derivative (C (c lam (n + 1) k) * (C 2 * X) ^ (n + 1 - 2 * k)) := by
    by_cases h : (n + 1) / 2 = n / 2
    · rw [h]
    · have hd : (n + 1) / 2 = n / 2 + 1 := by omega
      have hz : n + 1 - 2 * (n / 2 + 1) = 0 := by omega
      rw [hd, Finset.sum_range_succ]
      simp [hz]
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n / 2 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have he : n + 1 - 2 * k = (n - 2 * k) + 1 := by omega
  rw [derivative_C_mul, he, derivative_pow_succ, derivative_C_mul, derivative_X, mul_one]
  calc
    _ = C (c lam (n + 1) k * ((n - 2 * k : ℕ) + 1 : R)) * C 2 *
        (C 2 * X) ^ (n - 2 * k) := by simp only [C_mul]; ring
    _ = _ := by rw [hc k hk']; simp only [C_mul]; ring

end Polynomial
