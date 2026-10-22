/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.DiscreteTransform
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Integration
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.NearBest

/-! # Clenshaw–Curtis quadrature
Integrate the extrema interpolant by applying exact Chebyshev moments to its
DCT-I coefficients. The geometric estimate here is the interpolation-derived
bound, not the sharper constant of ATAP Theorem 19.3.
References: ATAP, Theorems 19.1--19.2 and 8.2.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open MeasureTheory Set Complex

/-- For `N>0`, Clenshaw–Curtis quadrature via the finite cosine transform (ATAP 19.2). -/
noncomputable def clenshawCurtis (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  if h : N = 0 then 2 * f 1 else
    ∑ k : Fin (N + 1),
      extremaCoefficient ⟨N, Nat.pos_of_ne_zero h⟩ f k * integralMoment k.val

/-- The coefficient formula integrates precisely the interpolating polynomial. -/
theorem clenshawCurtis_eq_integral_dctInterpolant (N : ℕ) (f : ℝ → ℝ) :
    clenshawCurtis N f = ∫ x in (-1 : ℝ)..1, (dctInterpolant N f).eval x := by
  by_cases hN : N = 0
  · subst N
    norm_num [clenshawCurtis, dctInterpolant, intervalIntegral.integral_const, mul_comm]
  · simp only [clenshawCurtis, dctInterpolant, dite_eq_right hN, eval_finsetSum,
      eval_mul, eval_C]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k _
      rw [intervalIntegral.integral_const_mul, integral_eval_T]
    · intro k _
      exact ((T ℝ (k.val : ℤ)).continuous.const_mul _).intervalIntegrable _ _

/-- The `(N+1)`-point rule is exact through degree `N` (ATAP 19.1). -/
theorem clenshawCurtis_eval {N : ℕ} (hN : N ≠ 0) {p : ℝ[X]} (hp : p.degree ≤ N) :
    clenshawCurtis N (fun x ↦ p.eval x) = ∫ x in (-1 : ℝ)..1, p.eval x := by
  rw [clenshawCurtis_eq_integral_dctInterpolant, dctInterpolant_eval hN hp]

/-- A uniform interpolation error controls the quadrature error by the interval length. -/
theorem abs_integral_sub_clenshawCurtis_le {N : ℕ} {f : ℝ → ℝ} {E : ℝ}
    (hf : IntervalIntegrable f volume (-1) 1)
    (he : ∀ x ∈ Icc (-1 : ℝ) 1, |f x - (dctInterpolant N f).eval x| ≤ E) :
    |(∫ x in (-1 : ℝ)..1, f x) - clenshawCurtis N f| ≤ 2 * E := by
  rw [clenshawCurtis_eq_integral_dctInterpolant,
    ← intervalIntegral.integral_sub hf ((dctInterpolant N f).continuous.intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 1) (f := fun x ↦ f x - (dctInterpolant N f).eval x)
    (fun x hx ↦ by
      rw [Real.norm_eq_abs]
      apply he x
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using uIoc_subset_uIcc hx)
  simpa only [Real.norm_eq_abs, sub_neg_eq_add, one_add_one_eq_two,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm] using h

/-- Real parts commute with extrema interpolation, linking the DCT to the
existing complex-valued interpolation API. -/
theorem eval_dctInterpolant_re {N : ℕ} (hN : N ≠ 0) (f : ℝ → ℂ) (x : ℝ) :
    (dctInterpolant N (fun t ↦ (f t).re)).eval x =
      ((extremaInterpolant N f).eval (x : ℂ)).re := by
  let n : {n : ℕ // 0 < n} := ⟨N,Nat.pos_of_ne_zero hN⟩
  rw [dctInterpolant_eq_lagrange n, extremaInterpolant_positive n]
  simp only [Lagrange.classicalInterpolate, Lagrange.interpolate_apply,
    eval_finsetSum, eval_mul, eval_C, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he := Lagrange.eval_classicalBasis_complex (Finset.range (N+1))
    (classicalNode n) j
    (Lagrange.BasisInput.of_injOn (strictAntiOn_classicalNode n).injOn hj) x
  simp only [Lagrange.classicalBasis] at he
  rw [he]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  rfl
/-- Baseline geometric Clenshaw–Curtis error, from ATAP 8.2. Analyticity is only
required in the open ellipse. No positivity theorem for the weights is assumed. -/
theorem abs_integral_sub_clenshawCurtis_le_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M) {N : ℕ} (hN : N ≠ 0) :
    |(∫ x in (-1 : ℝ)..1, (F x).re) - clenshawCurtis N (fun x ↦ (F x).re)| ≤
      8 * M / (ρ ^ N * (ρ - 1)) := by
  have hc : ContinuousOn (fun x : ℝ ↦ (F x).re) (Icc (-1) 1) :=
    Complex.continuous_re.continuousOn.comp
      (hF.continuousOn.comp Complex.continuous_ofReal.continuousOn
        (fun x hx ↦ ofReal_mem_bernsteinEllipse hρ hx)) (fun _ _ ↦ mem_univ _)
  have hi : IntervalIntegrable (fun x : ℝ ↦ (F x).re) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hc)
  have h := abs_integral_sub_clenshawCurtis_le hi (E := 4 * M / (ρ ^ N * (ρ - 1)))
    (fun x hx ↦ by
      rw [eval_dctInterpolant_re hN]
      exact (abs_re_le_norm (F x - (extremaInterpolant N (fun t ↦ F t)).eval (x : ℂ))).trans
        (norm_sub_extremaInterpolant_le_of_analytic hρ hF hM hN hx))
  convert h using 1
  ring

/-- The singleton interpolant integrates to twice its sole sample. -/
theorem clenshawCurtis_zero (f : ℝ → ℝ) : clenshawCurtis 0 f = 2 * f 1 := by
  simp [clenshawCurtis]

end Polynomial.Chebyshev
