/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClassicalNodes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Aliasing at the Chebyshev extrema

Frequencies are folded modulo `2N` into `[0,N]`. Reference: ATAP, Chapter 4.
-/

public section

namespace Polynomial.Chebyshev

open Real Set

/-- The degree obtained by folding a frequency into `[0,N]` (ATAP, Chapter 4). -/
def aliasIndex (N k : ℕ) : ℕ :=
  if N = 0 then 0 else min (k % (2 * N)) (2 * N - k % (2 * N))

/-- The singleton grid folds all modes to its constant mode. -/
theorem aliasIndex_zero (k : ℕ) : aliasIndex 0 k = 0 := by simp [aliasIndex]

/-- Classical frequency folding uses a strictly positive modulus. -/
theorem aliasIndex_positive (N : {n : ℕ // 0 < n}) (k : ℕ) :
    aliasIndex N.val k = min (k % (2 * N.val)) (2 * N.val - k % (2 * N.val)) := by
  simp [aliasIndex, Nat.ne_of_gt N.property]


/-- A folded frequency has degree at most the interpolation degree. -/
theorem aliasIndex_le {N : ℕ} (hN : N ≠ 0) (k : ℕ) : aliasIndex N k ≤ N := by
  have hmod := Nat.mod_lt k (show 0 < 2 * N by omega)
  simp only [aliasIndex, ite_eq_right hN]
  omega

/-- Frequencies at or below the interpolation degree are unchanged. -/
theorem aliasIndex_eq_self {N k : ℕ} (hN : N ≠ 0) (hk : k ≤ N) : aliasIndex N k = k := by
  simp only [aliasIndex, ite_eq_right hN]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem eval_T_node_mod {N : ℕ} (hN : N ≠ 0) (k j : ℕ) :
    (T ℝ k).eval (node N j) = (T ℝ (k % (2 * N) : ℕ)).eval (node N j) := by
  simp only [node, T_real_cos, Int.cast_natCast]
  have he : (k : ℝ) = (k % (2 * N) : ℕ) + (2 * N : ℕ) * (k / (2 * N) : ℕ) := by
    exact_mod_cast (Nat.mod_add_div k (2 * N)).symm
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hang : (k : ℝ) * (j * π / N) =
      (k % (2 * N) : ℕ) * (j * π / N) + (k / (2 * N) * j : ℕ) * (2 * π) := by
    rw [he]
    push_cast
    field_simp
  rw [hang, cos_add_nat_mul_two_pi]


/-- Folding a frequency at the extrema preserves its parity (ATAP, Chapter 4). -/
theorem aliasIndex_mod_two {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    aliasIndex N k % 2 = k % 2 := by
  have hm := Nat.mod_lt k (show 0 < 2 * N by omega)
  have hp : (k % (2 * N)) % 2 = k % 2 :=
    Nat.mod_mod_of_dvd k (dvd_mul_right 2 N)
  simp only [aliasIndex, ite_eq_right hN]
  rcases le_total (k % (2 * N)) (2 * N - k % (2 * N)) with h | h
  · rw [min_eq_left h]
    exact hp
  · rw [min_eq_right h]
    omega

/-- Node-level aliasing with the positive order in the node type (ATAP, Chapter 4). -/
theorem eval_T_node_aliasIndex (N : {n : ℕ // 0 < n}) (k j : ℕ) :
    (T ℝ k).eval (classicalNode N j) =
      (T ℝ (aliasIndex N.val k)).eval (classicalNode N j) := by
  rcases N with ⟨N,hNp⟩
  have hN := Nat.ne_of_gt hNp
  change (T ℝ k).eval (node N j) = (T ℝ (aliasIndex N k)).eval (node N j)
  rw [eval_T_node_mod hN]
  have hmod := Nat.mod_lt k (show 0 < 2 * N by omega)
  rw [aliasIndex_positive ⟨N,hNp⟩]
  dsimp only
  by_cases hk : k % (2 * N) ≤ N
  · rw [min_eq_left (by omega)]
  · rw [min_eq_right (by omega)]
    simp only [node, T_real_cos, Int.cast_natCast]
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hang : ((2 * N - k % (2 * N) : ℕ) : ℝ) * (j * π / N) =
        (j : ℝ) * (2 * π) - (k % (2 * N) : ℕ) * (j * π / N) := by
      rw [Nat.cast_sub hmod.le]
      push_cast
      field_simp
    rw [hang, cos_nat_mul_two_pi_sub]
end Polynomial.Chebyshev
