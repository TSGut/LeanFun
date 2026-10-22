/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring

/-!
# Gegenbauer parity and values at zero

References: DLMF Table 18.6.1 and the explicit sum 18.5.10.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Gegenbauer parity holds at every parameter (DLMF Table 18.6.1). -/
theorem gegenbauer_comp_neg_X (lam : R) (n : ℕ) :
    (gegenbauer lam n).comp (-X) = C ((-1 : R) ^ n) * gegenbauer lam n := by
  unfold gegenbauer
  rw [sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : 2 * k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  have hs : (-1 : R[X]) ^ (n - 2 * k) = (-1 : R[X]) ^ n := by
    nth_rw 2 [← Nat.sub_add_cancel hk']
    rw [pow_add, pow_mul]
    simp
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  rw [show C (2 : R) * (-X) = -(C 2 * X) by ring]
  rw [neg_pow (C (2 : R) * X), hs]
  simp only [map_pow, map_neg, map_one]
  ring

/-- Evaluation form of the parity identity (DLMF Table 18.6.1). -/
theorem eval_gegenbauer_neg (lam x : R) (n : ℕ) :
    (gegenbauer lam n).eval (-x) = (-1 : R) ^ n * (gegenbauer lam n).eval x := by
  have h := congrArg (fun p : R[X] => p.eval x) (gegenbauer_comp_neg_X lam n)
  simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] using h

/-- Even-index values at zero (DLMF Table 18.6.1). -/
theorem eval_gegenbauer_even_zero (lam : R) (m : ℕ) :
    (gegenbauer lam (2 * m)).eval 0 = (-1 : R) ^ m *
      algebraMap ℚ R ((m.factorial : ℚ)⁻¹) * (ascPochhammer R m).eval lam := by
  unfold gegenbauer
  rw [eval_finsetSum, Finset.sum_eq_single m]
  · simp [show 2 * m - m = m by omega]
  · intro k hk hkm
    have he : 2 * m - 2 * k ≠ 0 := by
      have := Finset.mem_range.mp hk
      omega
    simp [he]
  · simp

/-- Odd-index values at zero (DLMF Table 18.6.1). -/
@[simp] theorem eval_gegenbauer_odd_zero (lam : R) (m : ℕ) :
    (gegenbauer lam (2 * m + 1)).eval 0 = 0 := by
  unfold gegenbauer
  rw [eval_finsetSum]
  apply Finset.sum_eq_zero
  intro k hk
  have he : 2 * m + 1 - 2 * k ≠ 0 := by
    have := Finset.mem_range.mp hk
    omega
  simp [he]

end Polynomial
