/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Barycentric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Trigonometric estimates for Chebyshev extrema interpolation

Elementary sine estimates bound the Lagrange polynomials in terms of distance
in the angle variable. Reference: ATAP, Chapter 15.
-/

public section
open Real Set

namespace Polynomial.Chebyshev

/-- Trigonometric form of the unnormalised nodal polynomial (ATAP, Chapter 5). -/
theorem eval_extremaNodal_cos (N : {n : ℕ // 0 < n}) (θ : ℝ) :
    (extremaNodal N).eval (cos θ) = -(N.val : ℝ) * sin θ * sin (N.val * θ) := by
  have hu : (U ℝ ((N.val : ℤ) - 1)).eval (cos θ) * sin θ = sin ((N.val : ℝ) * θ) := by
    simp [U_real_cos]
  simp only [extremaNodal, eval_mul, eval_sub, eval_pow, eval_X, eval_one,
    T_derivative_eq_U, eval_natCast, Int.cast_natCast]
  rw [show cos θ ^ 2 - 1 = -(sin θ ^ 2) by nlinarith [sin_sq_add_cos_sq θ]]
  linear_combination -(N.val : ℝ) * sin θ * hu

/-- Cosine spacing controls the sine-weighted angular distance on `[0,π]`
(ATAP, Chapter 15, elementary trigonometric estimate). -/
theorem sin_mul_abs_sub_le_pi_mul_abs_cos_sub {θ φ : ℝ}
    (hθ : θ ∈ Icc 0 π) (hφ : φ ∈ Icc 0 π) :
    sin θ * |θ - φ| ≤ π * |cos θ - cos φ| := by
  have hmid : (sin θ + sin φ) / 2 ≤ sin ((θ + φ) / 2) := by
    convert strictConcaveOn_sin_Icc.concaveOn.2 hθ hφ
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1) using 1 <;>
      simp only [smul_eq_mul] <;> congr 1 <;> ring
  have hc : sin θ ≤ 2 * sin ((θ + φ) / 2) := by
    linarith [sin_nonneg_of_nonneg_of_le_pi hφ.1 hφ.2]
  have ha : |(θ - φ) / 2| ≤ π / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_div_iff_of_pos_right (by norm_num)).mpr
      (abs_le.mpr ⟨by linarith [hθ.1, hφ.2], by linarith [hθ.2, hφ.1]⟩)
  have hs := mul_abs_le_abs_sin ha
  have hd : |θ - φ| ≤ π * |sin ((θ - φ) / 2)| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
    have := (mul_le_mul_of_nonneg_left hs pi_pos.le)
    field_simp at this
    nlinarith
  have hsa : 0 ≤ sin ((θ + φ) / 2) := sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hθ.1, hφ.1]) (by linarith [hθ.2, hφ.2])
  calc
    _ ≤ (2 * sin ((θ + φ) / 2)) * (π * |sin ((θ - φ) / 2)|) :=
      mul_le_mul hc hd (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [cos_sub_cos, abs_mul, abs_mul, abs_of_nonneg hsa]
      norm_num
      ring

/-- The angle of an extrema node belongs to `[0,π]` (ATAP, Chapter 4). -/
theorem node_angle_mem_Icc {N j : ℕ} (hN : N ≠ 0) (hj : j ≤ N) :
    (j : ℝ) * π / N ∈ Icc 0 π := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  constructor
  · positivity
  · apply (div_le_iff₀ hn).mpr
    nlinarith [show (j : ℝ) ≤ N by exact_mod_cast hj, pi_pos]

/-- A cardinal polynomial, weighted by angular distance, is controlled by the
oscillatory sine numerator (ATAP, Chapter 15). -/
theorem abs_eval_extremaBasis_mul_angle_le {N j : ℕ} (hN : N ≠ 0) (hj : j ≤ N)
    {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    |(Lagrange.basis (Finset.range (N + 1)) (node N) j).eval (cos θ)| *
      (N : ℝ) * |θ - (j : ℝ) * π / N| ≤ π * |sin ((N : ℝ) * θ)| := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hφ := node_angle_mem_Icc hN hj
  have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  by_cases hx : cos θ = node N j
  · have ht : θ = (j : ℝ) * π / N :=
      strictAntiOn_cos.injOn hθ hφ hx
    simp only [ht, sub_self, abs_zero, mul_zero]
    positivity
  have hc : 0 < |cos θ - node N j| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have he :
      |(Lagrange.basis (Finset.range (N + 1)) (node N) j).eval (cos θ)| *
        (N : ℝ) * |cos θ - node N j| * extremaEndpointFactor ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩ =
      sin θ * |sin ((N : ℝ) * θ)| := by
    have hb := eval_extremaBasis ⟨N,Nat.pos_of_ne_zero hN⟩
      ⟨j,Nat.lt_succ_of_le hj⟩ ⟨cos θ,hx⟩
    change (Lagrange.basis (Finset.range (N+1)) (node N) j).eval (cos θ) = _ at hb
    dsimp only [classicalNode] at hb
    rw [hb, eval_extremaNodal_cos]
    simp only [abs_div, abs_mul, abs_neg, abs_of_nonneg hn.le,
      abs_of_nonneg hsin, abs_pow,
      abs_of_pos (extremaEndpointFactor_pos ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩)]
    field_simp [hn.ne', hc.ne', (extremaEndpointFactor_pos ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩).ne']
    ring
  have hE : 1 ≤ extremaEndpointFactor ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩ := by
    unfold extremaEndpointFactor
    split_ifs <;> norm_num
  have hsmall :
      |(Lagrange.basis (Finset.range (N + 1)) (node N) j).eval (cos θ)| *
        (N : ℝ) * |cos θ - node N j| ≤ sin θ * |sin ((N : ℝ) * θ)| := by
    rw [← he]
    exact le_mul_of_one_le_right (by positivity) hE
  have hspace := sin_mul_abs_sub_le_pi_mul_abs_cos_sub hθ hφ
  change sin θ * |θ - (j : ℝ) * π / N| ≤ π * |cos θ - node N j| at hspace
  have hh := mul_le_mul_of_nonneg_right hsmall (abs_nonneg (θ - (j : ℝ) * π / N))
  have hh' := mul_le_mul_of_nonneg_right hspace (abs_nonneg (sin ((N : ℝ) * θ)))
  apply (mul_le_mul_iff_left₀ hc).mp
  nlinarith

/-- Every cardinal polynomial is bounded by `π` on the angle interval
(ATAP, Chapter 15, nonsharp bound). -/
theorem abs_eval_extremaBasis_cos_le_pi {N j : ℕ} (hN : N ≠ 0) (hj : j ≤ N)
    {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    |(Lagrange.basis (Finset.range (N + 1)) (node N) j).eval (cos θ)| ≤ π := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  by_cases hx : cos θ = node N j
  · rw [hx, Lagrange.eval_basis_self (strictAntiOn_node N).injOn
      (Finset.mem_range.mpr (by omega)), abs_one]
    linarith [two_le_pi]
  have ht : θ ≠ (j : ℝ) * π / N := by
    intro ht
    exact hx (congrArg cos ht)
  have hd : 0 < |θ - (j : ℝ) * π / N| := abs_pos.mpr (sub_ne_zero.mpr ht)
  have hs : |sin ((N : ℝ) * θ)| ≤ (N : ℝ) * |θ - (j : ℝ) * π / N| := by
    have h := abs_sin_sub_sin_le ((N : ℝ) * θ) ((j : ℝ) * π)
    rw [sin_nat_mul_pi, sub_zero] at h
    have he : (N : ℝ) * θ - j * π = N * (θ - j * π / N) := by field_simp
    simpa [he, abs_mul, abs_of_pos hn] using h
  have h := (abs_eval_extremaBasis_mul_angle_le hN hj hθ).trans
    (mul_le_mul_of_nonneg_left hs pi_pos.le)
  apply (mul_le_mul_iff_left₀ (mul_pos hn hd)).mp
  nlinarith

end Polynomial.Chebyshev
