/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.SeriesCalculus
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.SeriesCoefficients
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Integration
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! # Anchored integration of absolutely convergent Chebyshev expansions
Use the existing sparse primitives, including their exceptional first two modes.
Reference: ATAP, Chapters 19 and 21.
-/

public section
namespace Polynomial.Chebyshev
open Complex Set MeasureTheory Filter

/-- The existing complex anchored primitive evaluates to the real-path integral. -/
theorem eval_primitiveTAt_eq_integral (n : ℕ) (x : ℝ) :
    (primitiveTAt (-1 : ℂ) n).eval (x : ℂ) = ∫ t in (-1 : ℝ)..x, (T ℂ n).eval (t : ℂ) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := x)
    (fun t _ ↦ ((primitiveT ℂ n).hasDerivAt (t : ℂ)).comp_ofReal)
    (f' := fun t : ℝ ↦ (primitiveT ℂ n).derivative.eval (t : ℂ))
    (by apply Continuous.intervalIntegrable; fun_prop)
  simpa only [derivative_primitiveT, primitiveTAt, eval_sub, eval_C, ofReal_neg, ofReal_one] using h.symm

/-- Anchored modes are uniformly bounded by the interval length. -/
theorem norm_eval_primitiveTAt_le_two (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖(primitiveTAt (-1 : ℂ) n).eval (x : ℂ)‖ ≤ 2 := by
  rw [eval_primitiveTAt_eq_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := x) (C := 1) (f := fun t : ℝ ↦ (T ℂ n).eval (t : ℂ))
    (fun t ht ↦ norm_eval_T_complex_le_one n (by
      rw [uIoc_of_le hx.1] at ht
      exact ⟨ht.1.le, ht.2.trans hx.2⟩))
  have he : |x - (-1)| ≤ 2 := by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
  exact h.trans (by simpa using he)

private theorem continuousOn_of_hasSum_chebyshev {a : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) {f : ℝ → ℂ}
    (hf : ∀ x : Icc (-1 : ℝ) 1, HasSum (fun n ↦ a n * (T ℂ n).eval (x.val : ℂ)) (f x.val)) :
    ContinuousOn f (Icc (-1 : ℝ) 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (continuousOn_complexChebyshevSeries ha).congr (fun x ↦
    complexChebyshevSeries_eq_of_tendsto (.ofAbsolute ha x) (hf x).tendsto_sum_nat)

/-- Termwise anchored integration, with actual integrability included. -/
theorem hasSum_primitiveTAt {a : ℕ → ℂ} (ha : Summable (fun n ↦ ‖a n‖))
    {f : ℝ → ℂ}
    (hf : ∀ x : Icc (-1 : ℝ) 1, HasSum (fun n ↦ a n * (T ℂ n).eval (x.val : ℂ)) (f x.val))
    (x : Icc (-1 : ℝ) 1) :
    IntervalIntegrable f volume (-1) x.val ∧
    HasSum (fun n ↦ a n * (primitiveTAt (-1 : ℂ) n).eval (x.val : ℂ))
      (∫ t in (-1 : ℝ)..x.val, f t) := by
  have hsub : uIcc (-1 : ℝ) x.val ⊆ Icc (-1 : ℝ) 1 := by
    rw [uIcc_of_le x.property.1]
    exact Icc_subset_Icc le_rfl x.property.2
  refine ⟨((continuousOn_of_hasSum_chebyshev ha hf).mono hsub).intervalIntegrable, ?_⟩
  have hb (n : ℕ) (t : ℝ) (ht : t ∈ uIcc (-1) x.val) :
      ‖a n * (T ℂ n).eval (t : ℂ)‖ ≤ ‖a n‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_T_complex_le_one n (hsub ht))
  have h := hasSum_integral_series (F := fun n t ↦ a n * (T ℂ n).eval (t : ℂ))
    (fun n ↦ by fun_prop) ha hb (fun t ht ↦ hf ⟨t, hsub ht⟩)
  simpa only [intervalIntegral.integral_const_mul, ← eval_primitiveTAt_eq_integral] using h

/-- The same absolute-tail bound for the actual anchored integral. -/
theorem norm_integral_sub_sum_primitiveTAt_le {a : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) {f : ℝ → ℂ}
    (hf : ∀ x : Icc (-1 : ℝ) 1, HasSum (fun n ↦ a n * (T ℂ n).eval (x.val : ℂ)) (f x.val))
    (x : Icc (-1 : ℝ) 1) (N : ℕ) :
    ‖(∫ t in (-1 : ℝ)..x.val, f t) -
      ∑ n ∈ Finset.range N, a n * (primitiveTAt (-1 : ℂ) n).eval (x.val : ℂ)‖ ≤
      2 * ∑' n, ‖a (n + N)‖ := by
  have h := norm_series_sub_sum_le_tail (hasSum_primitiveTAt ha hf x).2 (ha.mul_left 2)
    (fun n ↦ by rw [norm_mul]; simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (norm_eval_primitiveTAt_le_two n x.property) (norm_nonneg (a n))) N
  simpa only [tsum_mul_left] using h

/-- Uniform convergence includes both endpoints of the typed interval. -/
theorem tendstoUniformlyOn_primitiveTAt {a : ℕ → ℂ} (ha : Summable (fun n ↦ ‖a n‖))
    {f : ℝ → ℂ}
    (hf : ∀ x : Icc (-1 : ℝ) 1, HasSum (fun n ↦ a n * (T ℂ n).eval (x.val : ℂ)) (f x.val)) :
    TendstoUniformly
      (fun N (x : Icc (-1 : ℝ) 1) ↦ ∑ n ∈ Finset.range N, a n * (primitiveTAt (-1 : ℂ) n).eval (x.val : ℂ))
      (fun x ↦ ∫ t in (-1 : ℝ)..x.val, f t) atTop := by
  have h := tendstoUniformlyOn_tsum_nat (s := Set.univ) (ha.mul_left 2)
    (fun n (x : Icc (-1 : ℝ) 1) _ ↦
      (show ‖a n * (primitiveTAt (-1 : ℂ) n).eval (x.val : ℂ)‖ ≤ 2 * ‖a n‖ by
        rw [norm_mul]; simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (norm_eval_primitiveTAt_le_two n x.property) (norm_nonneg (a n))))
  exact tendstoUniformlyOn_univ.mp (h.congr_right (fun x _ ↦ (hasSum_primitiveTAt ha hf x).2.tsum_eq))

/-- Geometric input coefficients give a geometric anchored-integration error,
uniformly including both endpoints. -/
theorem norm_integral_sub_sum_primitiveTAt_le_geometric {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    {f : ℝ → ℂ}
    (hf : ∀ x : Icc (-1 : ℝ) 1, HasSum (fun n ↦ a n * (T ℂ n).eval (x.val : ℂ)) (f x.val))
    (x : Icc (-1 : ℝ) 1) (N : ℕ) :
    ‖(∫ t in (-1 : ℝ)..x.val, f t) -
      ∑ n ∈ Finset.range N, a n * (primitiveTAt (-1 : ℂ) n).eval (x.val : ℂ)‖ ≤
      2 * (C * (ρ⁻¹) ^ N / (1 - ρ⁻¹)) := by
  have hq0 : 0 ≤ ρ⁻¹ := by positivity
  have hq1 : ρ⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < ρ)).2 hρ
  have hb (n : ℕ) : ‖a n‖ ≤ C * (ρ⁻¹) ^ n := by
    simpa only [inv_pow, div_eq_mul_inv] using ha n
  have hs := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
    ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
  exact (norm_integral_sub_sum_primitiveTAt_le hs hf x N).trans
    (mul_le_mul_of_nonneg_left
      (tsum_tail_le_geometric hq0 hq1 (fun _ ↦ norm_nonneg _) hb N) (by norm_num))

end Polynomial.Chebyshev
