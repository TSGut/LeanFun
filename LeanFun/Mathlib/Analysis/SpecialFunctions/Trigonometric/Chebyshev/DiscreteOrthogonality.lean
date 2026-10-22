/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Aliasing
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Discrete Chebyshev orthogonality
The extrema grid carries half weight at each endpoint. These finite sums are
exact real identities; they do not assume rational cosine values.
Reference: ATAP, Chapter 4 (the discrete cosine transform).
-/

@[expose] public section
namespace Polynomial.Chebyshev
open Real

/-- The endpoint-half-weighted sum on the extrema indices `0,...,N`.
This is the usual double-primed sum at positive order. -/
noncomputable def extremaSum (N : {n : ℕ // 0 < n}) (f : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range N.val, f j) + (f N.val - f 0) / 2

/-- Weighted sums preserve addition (ATAP, Chapter 4). -/
theorem extremaSum_add (N : {n : ℕ // 0 < n}) (f g : ℕ → ℝ) :
    extremaSum N (fun j ↦ f j + g j) = extremaSum N f + extremaSum N g := by
  simp only [extremaSum, Finset.sum_add_distrib]
  ring

/-- Weighted sums preserve real scalar multiplication (ATAP, Chapter 4). -/
theorem extremaSum_mul (N : {n : ℕ // 0 < n}) (a : ℝ) (f : ℕ → ℝ) :
    extremaSum N (fun j ↦ a * f j) = a * extremaSum N f := by
  simp only [extremaSum, ← Finset.mul_sum]
  ring

/-- The constant function has weighted sum `N`. -/
@[simp] theorem extremaSum_one (N : {n : ℕ // 0 < n}) : extremaSum N (fun _ ↦ 1) = N.val := by
  simp [extremaSum]

private theorem sin_mul_extremaSum_cos (N : ℕ) (hN : 0 < N) (θ : ℝ) :
    sin (θ / 2) * extremaSum ⟨N, by omega⟩ (fun j ↦ cos (θ * j)) =
      sin (N * θ) * cos (θ / 2) / 2 := by
  have hs := sin_mul_sum_cos N θ 0
  simp only [add_zero] at hs
  have he : ((N : ℝ) - 1) * θ / 2 = (N : ℝ) * θ / 2 - θ / 2 := by ring
  rw [he, cos_sub] at hs
  have ht : (N : ℝ) * θ = 2 * ((N : ℝ) * θ / 2) := by ring
  dsimp [extremaSum]
  simp only [Nat.cast_zero, mul_zero, cos_zero]
  rw [mul_add, hs]
  conv_rhs => rw [ht, sin_two_mul]
  rw [show θ * (N : ℝ) = 2 * ((N : ℝ) * θ / 2) by ring, cos_two_mul]
  linear_combination sin (θ / 2) * (sin_sq_add_cos_sq ((N : ℝ) * θ / 2))

/-- Every nonconstant cosine frequency below `2N` has zero weighted sum. -/
theorem extremaSum_cos_eq_zero {N k : ℕ} (hk : 0 < k) (hkN : k < 2 * N) :
    extremaSum ⟨N, by omega⟩ (fun j ↦ cos ((k * π / N) * j)) = 0 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkN' : (k : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hkN
  have hs := sin_mul_extremaSum_cos N (by omega) (k * π / N)
  have he : (N : ℝ) * (k * π / N) = k * π := by field_simp
  rw [he, sin_nat_mul_pi, zero_mul, zero_div] at hs
  have hp : 0 < sin ((k * π / N) / 2) := by
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (div_lt_iff₀ hN).2
    nlinarith [pi_pos]
  exact (mul_eq_zero.mp hs).resolve_left hp.ne'

/-- The weighted discrete mean of a Chebyshev polynomial below frequency `2N`. -/
theorem extremaSum_eval_T {N k : ℕ} (hk : k < 2 * N) :
    extremaSum ⟨N, by omega⟩ (fun j ↦ (T ℝ k).eval (node N j)) = if k = 0 then (N : ℝ) else 0 := by
  by_cases h : k = 0
  · subst k
    simp
  · rw [ite_eq_right h]
    convert extremaSum_cos_eq_zero (Nat.pos_of_ne_zero h) hk using 1
    congr 1
    funext j
    simp only [node, T_real_cos, Int.cast_natCast]
    congr 1
    ring

/-- Frequency `2N` is the constant nodal mode, including its endpoint weights. -/
theorem extremaSum_eval_T_two_mul {N : ℕ} (hN : N ≠ 0) :
    extremaSum ⟨N, by omega⟩ (fun j ↦ (T ℝ (2 * N : ℕ)).eval (node N j)) = N := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have he (j : ℕ) : (T ℝ (2 * N : ℕ)).eval (node N j) = 1 := by
    simp only [node, T_real_cos]
    push_cast
    rw [show 2 * (N : ℝ) * (j * π / N) = j * (2 * π) by field_simp]
    exact cos_nat_mul_two_pi j
  simp_rw [he]
  exact extremaSum_one ⟨N, by omega⟩

private theorem extremaSum_product {N j k : ℕ} (hN : 0 < N) (hkj : k ≤ j) :
    2 * extremaSum ⟨N, by omega⟩ (fun m ↦ (T ℝ j).eval (node N m) * (T ℝ k).eval (node N m)) =
      extremaSum ⟨N, by omega⟩ (fun m ↦ (T ℝ (j + k : ℕ)).eval (node N m)) +
      extremaSum ⟨N, by omega⟩ (fun m ↦ (T ℝ (j - k : ℕ)).eval (node N m)) := by
  have he : (fun m ↦ 2 * ((T ℝ j).eval (node N m) * (T ℝ k).eval (node N m))) =
      (fun m ↦ (T ℝ (j + k : ℕ)).eval (node N m) +
        (T ℝ (j - k : ℕ)).eval (node N m)) := by
    funext m
    have h := congrArg (fun p : ℝ[X] ↦ p.eval (node N m)) (T_mul_T ℝ j k)
    simpa only [eval_mul, eval_ofNat, eval_add, Nat.cast_add, Nat.cast_sub hkj,
      mul_assoc] using h
  have h := congrArg (extremaSum ⟨N, by omega⟩) he
  simpa only [extremaSum_mul, extremaSum_add] using h

/-- Distinct Chebyshev modes through degree `N` are discretely orthogonal. -/
theorem extremaSum_mul_eval_T_eq_zero {N j k : ℕ}
    (hj : j ≤ N) (hk : k ≤ N) (hjk : j ≠ k) :
    extremaSum ⟨N, by omega⟩ (fun m ↦ (T ℝ j).eval (node N m) * (T ℝ k).eval (node N m)) = 0 := by
  wlog hkj : k ≤ j generalizing j k
  · have h := this hk hj hjk.symm (by omega)
    simpa only [mul_comm] using h
  have h := extremaSum_product (N := N) (by omega) hkj
  rw [extremaSum_eval_T (by omega : j + k < 2 * N),
    extremaSum_eval_T (by omega : j - k < 2 * N),
    ite_eq_right (by omega : j + k ≠ 0), ite_eq_right (by omega : j - k ≠ 0)] at h
  linarith

/-- Endpoint modes have discrete squared norm `N`, and all interior modes `N/2`. -/
theorem extremaSum_sq_eval_T {N k : ℕ} (hN : N ≠ 0) (hk : k ≤ N) :
    extremaSum ⟨N, by omega⟩ (fun m ↦ (T ℝ k).eval (node N m) ^ 2) =
      if k = 0 ∨ k = N then (N : ℝ) else N / 2 := by
  have h := extremaSum_product (N := N) (j := k) (k := k) (Nat.pos_of_ne_zero hN) le_rfl
  simp only [Nat.sub_self, Nat.cast_zero, T_zero, eval_one, extremaSum_one] at h
  by_cases hzero : k = 0
  · subst k
    simp
  · by_cases hlast : k = N
    · subst k
      rw [show N + N = 2 * N by omega, extremaSum_eval_T_two_mul hN] at h
      rw [ite_eq_left (Or.inr rfl)]
      simpa only [pow_two] using (show extremaSum ⟨N, by omega⟩
        (fun m ↦ (T ℝ N).eval (node N m) * (T ℝ N).eval (node N m)) = N by linarith)
    · rw [extremaSum_eval_T (by omega : k + k < 2 * N),
        ite_eq_right (by omega : k + k ≠ 0)] at h
      rw [ite_eq_right (by simp [hzero, hlast])]
      simpa only [pow_two] using (show extremaSum ⟨N, by omega⟩
        (fun m ↦ (T ℝ k).eval (node N m) * (T ℝ k).eval (node N m)) = (N : ℝ) / 2 by linarith)

end Polynomial.Chebyshev
