/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.SeriesRepresentation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.AnalyticDecay

/-!
# Complex Chebyshev series and geometric truncation

Representation and the projection estimate of ATAP, Theorem 8.2.
-/

public section

namespace Polynomial.Chebyshev

open Real Set MeasureTheory Complex

/-- An absolutely summable complex Chebyshev series represents its continuous
function on the closed interval (ATAP, Chapters 4 and 8). -/
theorem hasSum_complexCoefficient_mul_eval_T {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1))
    (ha : Summable (fun n ↦ ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n))‖))
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    HasSum (fun n : ℕ ↦ (complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n)) * (((T ℝ n).eval x : ℝ) : ℂ)) (f x) := by
  have hr : Summable (fun n ↦ |(coefficient (n := n) ⟨(fun x ↦ (f x).re), by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩)|) :=
    ha.of_norm_bounded fun n ↦ by
      simpa only [Real.norm_eq_abs, abs_abs, ← complexCoefficient_re hf n] using
        Complex.abs_re_le_norm ((complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n)))
  have hi : Summable (fun n ↦ |(coefficient (n := n) ⟨(fun x ↦ (f x).im), by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩)|) :=
    ha.of_norm_bounded fun n ↦ by
      simpa only [Real.norm_eq_abs, abs_abs, ← complexCoefficient_im hf n] using
        Complex.abs_im_le_norm ((complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n)))
  apply (Complex.hasSum_iff _ _).2
  constructor
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      complexCoefficient_re hf] using
      hasSum_coefficient_mul_eval_T (f := fun x ↦ (f x).re) (Complex.continuous_re.comp_continuousOn hf) hr hx
  · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      complexCoefficient_im hf] using
      hasSum_coefficient_mul_eval_T (f := fun x ↦ (f x).im) (Complex.continuous_im.comp_continuousOn hf) hi hx

/-- Absolute coefficient tails bound complex Chebyshev truncations (ATAP, equation 4.8). -/
theorem norm_sub_sum_complex_le_tsum_tail {a : ℕ → ℂ} {y : ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) {x : ℝ} (hx : x ∈ Icc (-1) 1)
    (hf : HasSum (fun n : ℕ ↦ a n * (((T ℝ n).eval x : ℝ) : ℂ)) y) (N : ℕ) :
    ‖y - ∑ n ∈ Finset.range (N + 1), a n * (((T ℝ n).eval x : ℝ) : ℂ)‖ ≤
      ∑' k, ‖a (k + (N + 1))‖ := by
  have h := norm_sub_sum_smul_le_tsum_tail (f := fun _ ↦ y) ha hx
    (by simpa only [Complex.real_smul, mul_comm] using hf) N
  simpa only [Complex.real_smul, mul_comm] using h

/-- Sum a shifted geometric majorant for coefficient tails (ATAP, Chapter 8). -/
theorem tsum_geometric_majorant_tail {C q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑' k : ℕ, C * q ^ (k + N)) = C * q ^ N / (1 - q) := by
  have he (k : ℕ) : C * q ^ (k + N) = (C * q ^ N) * q ^ k := by
    rw [pow_add]
    ring
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1]
  ring

/-- A nonnegative sequence with a geometric majorant has the corresponding tail bound. -/
theorem tsum_tail_le_geometric {b : ℕ → ℝ} {C q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hb : ∀ n, 0 ≤ b n)
    (hbound : ∀ n, b n ≤ C * q ^ n) (N : ℕ) :
    (∑' k, b (k + N)) ≤ C * q ^ N / (1 - q) := by
  have hg := (summable_geometric_of_lt_one hq hq1).mul_left C
  have hs : Summable b := Summable.of_nonneg_of_le hb hbound hg
  calc
    _ ≤ ∑' k, C * q ^ (k + N) :=
      ((summable_nat_add_iff N).2 hs).tsum_le_tsum (fun k ↦ hbound _)
        ((summable_nat_add_iff N).2 hg)
    _ = C * q ^ N / (1 - q) := tsum_geometric_majorant_tail hq hq1 N

/-- A geometric coefficient bound gives the complex truncation bound once the
series represents the function (ATAP, Theorem 8.2). -/
theorem norm_sub_sum_complex_le_geometric {a : ℕ → ℂ} {y : ℂ} {C q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (ha : ∀ n, ‖a n‖ ≤ C * q ^ n)
    {x : ℝ} (hx : x ∈ Icc (-1) 1)
    (hf : HasSum (fun n : ℕ ↦ a n * (((T ℝ n).eval x : ℝ) : ℂ)) y) (N : ℕ) :
    ‖y - ∑ n ∈ Finset.range (N + 1), a n * (((T ℝ n).eval x : ℝ) : ℂ)‖ ≤
      C * q ^ (N + 1) / (1 - q) := by
  have hg := (summable_geometric_of_lt_one hq hq1).mul_left C
  have hs : Summable (fun n ↦ ‖a n‖) :=
    hg.of_norm_bounded (fun n ↦ by simpa only [norm_norm] using ha n)
  exact (norm_sub_sum_complex_le_tsum_tail hs hx hf N).trans
    (tsum_tail_le_geometric hq hq1 (fun n ↦ norm_nonneg (a n)) ha (N + 1))

/-- Geometric truncation error for a function bounded and analytic in an open
Bernstein ellipse; no boundary continuity is assumed (ATAP, Theorem 8.2). -/
theorem norm_sub_sum_complexCoefficient_le_of_analytic {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ⟨ρ, hρ⟩))
    (hb : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖f z‖ ≤ M)
    {x : ℝ} (hx : x ∈ Icc (-1) 1) (N : ℕ) :
    ‖f x - ∑ n ∈ Finset.range (N + 1),
      (complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun t : ℝ ↦ f t) (continuousOn_real_of_analytic hρ hf) n)) * (((T ℝ n).eval x : ℝ) : ℂ)‖ ≤
      2 * M / (ρ ^ N * (ρ - 1)) := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hb x (ofReal_mem_bernsteinEllipse hρ hx))
  have hq : ρ⁻¹ < 1 := (inv_lt_one₀ hρ0).2 hρ
  have hc : ContinuousOn (fun t : ℝ ↦ f t) (Icc (-1) 1) :=
    hf.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun t ht ↦ ofReal_mem_bernsteinEllipse hρ ht)
  have hcoeff (n : ℕ) : ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun t : ℝ ↦ f t) (continuousOn_real_of_analytic hρ hf) n))‖ ≤ (2 * M) * (ρ⁻¹) ^ n := by
    apply (norm_complexCoefficient_le_of_analytic hρ hf hb n).trans
    rw [inv_pow, div_eq_mul_inv]
    gcongr
    split_ifs <;> norm_num
  have hs : Summable (fun n ↦ ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun t : ℝ ↦ f t) (continuousOn_real_of_analytic hρ hf) n))‖) :=
    ((summable_geometric_of_lt_one (inv_nonneg.mpr hρ0.le) hq).mul_left (2 * M)).of_norm_bounded
      (fun n ↦ by simpa only [norm_norm] using hcoeff n)
  apply (norm_sub_sum_complex_le_geometric (inv_nonneg.mpr hρ0.le) hq hcoeff hx
    (hasSum_complexCoefficient_mul_eval_T hc hs hx) N).trans_eq
  rw [inv_pow, pow_succ]
  field_simp

end Polynomial.Chebyshev
