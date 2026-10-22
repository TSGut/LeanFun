/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.LinearAlgebra.Lagrange

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The polynomial vanishing at Chebyshev extrema

The polynomial `(X² - 1) T'_N` is a nonzero scalar multiple of the monic
nodal polynomial. Its derivative determines the alternating barycentric weights.
Reference: ATAP, Chapter 5.
-/

@[expose] public section

namespace Polynomial.Chebyshev
open Real

/-- An unnormalised nodal polynomial for the extrema (ATAP, Chapter 5). -/
noncomputable def extremaNodal (N : {n : ℕ // 0 < n}) : ℝ[X] :=
  (X ^ 2 - 1) * derivative (T ℝ N.val)

/-- The endpoint factor in the reciprocal barycentric weights (ATAP, Chapter 5). -/
def extremaEndpointFactor (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) : ℝ :=
  if j.val = 0 ∨ j.val = N.val then 2 else 1

/-- The derivative vanishes at the interior extrema (ATAP, Chapters 3 and 5). -/
theorem eval_derivative_T_node {N j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    (derivative (T ℝ N)).eval (node N j) = 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hφ0 : 0 < (j : ℝ) * π / N := by positivity
  have hφπ : (j : ℝ) * π / N < π := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < N)).mpr
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hjN) pi_pos |>.trans_eq (mul_comm _ _)
  have hs := (sin_pos_of_pos_of_lt_pi hφ0 hφπ).ne'
  apply (mul_eq_zero.mp (show (derivative (T ℝ N)).eval (node N j) *
      sin ((j : ℝ) * π / N) = 0 from ?_)).resolve_right hs
  rw [T_derivative_eq_U]
  simp only [eval_mul, eval_intCast, node, mul_assoc]
  rw [U_real_cos]
  push_cast
  rw [sub_add_cancel]
  have ha : (N : ℝ) * (j * π / N) = j * π := by field_simp
  rw [ha, sin_nat_mul_pi, mul_zero]

/-- The nodal polynomial vanishes at every interpolation node (ATAP, Chapter 5). -/
theorem eval_extremaNodal_node {N j : ℕ} (hN : N ≠ 0) (hj : j ≤ N) :
    (extremaNodal ⟨N, by omega⟩).eval (node N j) = 0 := by
  by_cases hj0 : j = 0
  · subst j; simp [extremaNodal, node_eq_one]
  by_cases hjN : j = N
  · subst j; simp [extremaNodal, node_eq_neg_one hN]
  simp [extremaNodal, eval_derivative_T_node (Nat.pos_of_ne_zero hj0) (by omega : j < N)]

/-- Derivative of the unnormalised nodal polynomial (ATAP, Chapter 5). -/
theorem eval_derivative_extremaNodal (N : {n : ℕ // 0 < n}) (x : ℝ) :
    (derivative (extremaNodal N)).eval x =
      x * (derivative (T ℝ N.val)).eval x + (N.val : ℝ) ^ 2 * (T ℝ N.val).eval x := by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := ℝ) (N.val : ℤ) 0 x
  simp at h
  simp only [extremaNodal, derivative_mul, derivative_sub, derivative_pow,
    derivative_X, derivative_one, mul_one, sub_zero, eval_add, eval_mul, eval_sub,
    eval_pow, eval_X, eval_one, eval_C]
  linear_combination -h

/-- The endpoint derivative is twice the interior derivative in magnitude
(ATAP, Chapter 5). -/
theorem eval_derivative_extremaNodal_node {N j : ℕ} (hN : N ≠ 0) (hj : j ≤ N) :
    (derivative (extremaNodal ⟨N, by omega⟩)).eval (node N j) =
      extremaEndpointFactor ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩ * (N : ℝ) ^ 2 * (-1) ^ j := by
  rw [eval_derivative_extremaNodal, eval_T_real_node (Finset.mem_Iic.mpr hj)]
  by_cases he : j = 0 ∨ j = N
  · have hx : (node N j) ^ 2 = 1 := by
      rcases he with rfl | rfl
      · simp [node_eq_one]
      · simp [node_eq_neg_one hN]
    have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := ℝ) (N : ℤ) 0 (node N j)
    simp only [hx, sub_self, zero_mul, Function.iterate_zero, Function.iterate_succ_apply,
      id_eq, zero_add, Int.cast_natCast,
      eval_T_real_node (Finset.mem_Iic.mpr hj)] at h
    simp only [extremaEndpointFactor, ite_eq_left he]
    linear_combination -h
  · have hd := eval_derivative_T_node (show 0 < j by omega) (show j < N by omega)
    simp [extremaEndpointFactor, he, hd]

/-- The nodal polynomial is nonzero for positive order (ATAP, Chapter 5). -/
theorem extremaNodal_ne_zero {N : ℕ} (hN : N ≠ 0) : extremaNodal ⟨N, by omega⟩ ≠ 0 := by
  intro h
  have hd := eval_derivative_extremaNodal_node hN (j := 0) (Nat.zero_le N)
  simp [h, extremaEndpointFactor, hN] at hd

/-- Degree bound for the unnormalised nodal polynomial (ATAP, Chapter 5). -/
theorem natDegree_extremaNodal_le {N : ℕ} (hN : N ≠ 0) :
    (extremaNodal ⟨N, by omega⟩).natDegree ≤ N + 1 := by
  have ht := natDegree_derivative_le (T ℝ (N : ℤ))
  rw [natDegree_T, Int.natAbs_natCast] at ht
  have hx : (X ^ 2 - 1 : ℝ[X]).natDegree ≤ 2 := by compute_degree
  exact (natDegree_mul_le.trans (Nat.add_le_add hx ht)).trans (by omega)

/-- The two nodal polynomials differ by their leading coefficient (ATAP, Chapter 5). -/
theorem extremaNodal_eq_leadingCoeff_mul_nodal {N : ℕ} (hN : N ≠ 0) :
    extremaNodal ⟨N, by omega⟩ = Polynomial.C (extremaNodal ⟨N, by omega⟩).leadingCoeff *
      Lagrange.nodal (Finset.range (N + 1)) (node N) := by
  let q := Lagrange.nodal (Finset.range (N + 1)) (node N)
  have hq : q ≠ 0 := Lagrange.nodal_ne_zero
  have hr : extremaNodal ⟨N, by omega⟩ % q = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      (Finset.range (N + 1)) (strictAntiOn_node N).injOn
    · simpa [q, Lagrange.degree_nodal] using degree_mod_lt (extremaNodal ⟨N, by omega⟩) hq
    · intro j hj
      have he := congrArg (fun p : ℝ[X] ↦ p.eval (node N j))
        (EuclideanDomain.div_add_mod (extremaNodal ⟨N, by omega⟩) q)
      simpa [q, Lagrange.eval_nodal_at_node hj,
        eval_extremaNodal_node hN (by simpa using hj)] using he
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    Lagrange.nodal_monic ((EuclideanDomain.mod_eq_zero).mp hr)
  simpa [Lagrange.natDegree_nodal] using natDegree_extremaNodal_le hN

end Polynomial.Chebyshev
