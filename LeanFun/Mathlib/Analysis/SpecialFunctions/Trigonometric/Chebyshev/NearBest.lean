/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Lebesgue

import Mathlib.Tactic.Ring

/-!
# Near-best Chebyshev interpolation

The error is at most `(1 + Λ_N)` times the uniform error of any degree-`N`
polynomial competitor. Functions and competitor polynomials may be complex-valued.
No continuity is needed when a pointwise uniform competitor bound is supplied.
Reference: ATAP, Chapter 16.
-/

public section

namespace Polynomial.Chebyshev
open Set


/-- The Lebesgue function controls evaluation in terms of nodal data
(ATAP, Chapter 15). -/
theorem norm_eval_extremaInterpolant_le (N : ℕ) (f : ℝ → ℂ) {M : ℝ}
    (hf : ∀ j : Fin (N + 1), ‖f (extremaGridNode N j)‖ ≤ M) (x : ℝ) :
    ‖(extremaInterpolant N f).eval (x : ℂ)‖ ≤ M * extremaLebesgueFunction N x := by
  rw [eval_extremaInterpolant]
  apply (norm_sum_le _ _).trans
  simp_rw [norm_mul]
  rw [extremaLebesgueFunction, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_right (hf j) (norm_nonneg _)

/-- Interpolation reproduces every polynomial of degree at most `N`
(ATAP, Chapter 4). -/
theorem extremaInterpolant_eq_self {N : ℕ} {p : ℂ[X]} (hp : p.degree < (N + 1 : ℕ)) :
    extremaInterpolant N (fun x : ℝ ↦ p.eval (x : ℂ)) = p := by
  by_cases h : N = 0
  · subst N
    have hp0 : p.degree ≤ 0 := by
      have hp' : p.degree < (1 : WithBot ℕ) := by simpa using hp
      revert hp'
      cases p.degree
      · exact fun _ ↦ bot_le
      · exact fun h ↦ WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ (WithBot.coe_lt_coe.mp h))
    have he := eq_C_of_degree_le_zero (p := p) hp0
    rw [extremaInterpolant_zero, he]
    simp
  · rw [extremaInterpolant_positive ⟨N,Nat.pos_of_ne_zero h⟩]
    symm
    apply Lagrange.eq_interpolate (v := fun j ↦ (classicalNode ⟨N,Nat.pos_of_ne_zero h⟩ j : ℂ))
      (Complex.ofReal_injective.comp_injOn (strictAntiOn_classicalNode ⟨N,Nat.pos_of_ne_zero h⟩).injOn)
    simpa only [Finset.card_range] using hp

/-- Interpolation commutes with subtraction (ATAP, Chapter 4). -/
theorem extremaInterpolant_sub (N : ℕ) (f g : ℝ → ℂ) :
    extremaInterpolant N (fun x ↦ f x - g x) =
      extremaInterpolant N f - extremaInterpolant N g := by
  by_cases h : N = 0
  · subst N
    simp only [extremaInterpolant_zero, map_sub]
  · simp only [extremaInterpolant_positive ⟨N,Nat.pos_of_ne_zero h⟩,
      Lagrange.classicalInterpolate]
    exact map_sub (Lagrange.interpolate (Finset.range (N+1))
      (fun j ↦ (classicalNode ⟨N,Nat.pos_of_ne_zero h⟩ j : ℂ))) _ _

/-- The pointwise near-best estimate for any uniformly accurate polynomial competitor
(ATAP, Chapter 16). -/
theorem norm_sub_extremaInterpolant_le_competitor {N : ℕ} {f : ℝ → ℂ} {p : ℂ[X]}
    (hp : p.degree < (N + 1 : ℕ)) {ε : ℝ}
    (hf : ∀ x ∈ Icc (-1) 1, ‖f x - p.eval (x : ℂ)‖ ≤ ε)
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    ‖f x - (extremaInterpolant N f).eval (x : ℂ)‖ ≤
      (1 + extremaLebesgueFunction N x) * ε := by
  have he := extremaInterpolant_sub N f (fun x : ℝ ↦ p.eval (x : ℂ))
  rw [extremaInterpolant_eq_self hp] at he
  have hi := norm_eval_extremaInterpolant_le N (fun t ↦ f t - p.eval (t : ℂ))
    (fun j ↦ hf _ (extremaGridNode_mem_Icc N j)) x
  rw [he, eval_sub] at hi
  have ht := norm_sub_le (f x - p.eval (x : ℂ))
    ((extremaInterpolant N f).eval (x : ℂ) - p.eval (x : ℂ))
  rw [sub_sub_sub_cancel_right] at ht
  nlinarith [hf x hx]

/-- Uniform near-best estimate using the bounded Lebesgue constant
(ATAP, Chapter 16). -/
theorem norm_sub_extremaInterpolant_le_lebesgueConstant {N : ℕ} {f : ℝ → ℂ} {p : ℂ[X]}
    (hp : p.degree < (N + 1 : ℕ)) {ε : ℝ}
    (hf : ∀ x ∈ Icc (-1) 1, ‖f x - p.eval (x : ℂ)‖ ≤ ε)
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    ‖f x - (extremaInterpolant N f).eval (x : ℂ)‖ ≤
      (1 + extremaLebesgueConstant N) * ε := by
  apply (norm_sub_extremaInterpolant_le_competitor hp hf hx).trans
  exact mul_le_mul_of_nonneg_right
    (add_le_add (le_refl 1) (extremaLebesgueFunction_le_constant N hx))
    ((norm_nonneg _).trans (hf x hx))

/-- An explicit logarithmic near-best factor for positive interpolation order
(ATAP, Chapter 16; nonsharp Lebesgue bound). -/
theorem norm_sub_extremaInterpolant_le_log_competitor {N : ℕ} (hN : N ≠ 0)
    {f : ℝ → ℂ} {p : ℂ[X]} (hp : p.degree < (N + 1 : ℕ)) {ε : ℝ}
    (hf : ∀ x ∈ Icc (-1) 1, ‖f x - p.eval (x : ℂ)‖ ≤ ε)
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    ‖f x - (extremaInterpolant N f).eval (x : ℂ)‖ ≤
      (2 * Real.pi + 3 + 2 * Real.log N) * ε := by
  apply (norm_sub_extremaInterpolant_le_lebesgueConstant hp hf hx).trans
  apply mul_le_mul_of_nonneg_right _ ((norm_nonneg _).trans (hf x hx))
  linarith [extremaLebesgueConstant_le_log hN]

end Polynomial.Chebyshev
