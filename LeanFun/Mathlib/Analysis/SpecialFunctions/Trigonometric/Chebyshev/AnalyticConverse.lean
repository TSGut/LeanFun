/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.EllipseGrowth
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexSeriesDomain
public import LeanFun.Mathlib.Analysis.Analytic.OpenDomain
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Analytic continuation from geometric Chebyshev decay
The series is analytic in the open ellipse and uniformly bounded on each
strictly smaller ellipse. Reference: ATAP, Theorems 8.1--8.3.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open Complex Set

private theorem term_norm_le {a : ℕ → ℂ} {C ρ r : ℝ} (hρ : 1 < ρ) (hr : 1 < r)
    (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) {z : ℂ} (hz : z ∈ bernsteinEllipse ⟨r, hr⟩) (n : ℕ) :
    ‖a n * (T ℂ n).eval z‖ ≤ C * (r / ρ) ^ n := by
  have hC : 0 ≤ C := (norm_nonneg (a 0)).trans (by simpa using ha 0)
  rw [norm_mul]
  calc
    _ ≤ (C / ρ ^ n) * r ^ n := mul_le_mul (ha n)
      (norm_eval_T_le_on_bernsteinEllipse hr hz n) (norm_nonneg _) (by positivity)
    _ = _ := by rw [div_pow]; ring

/-- On a strictly smaller ellipse, geometric coefficient decay makes the
Chebyshev terms absolutely summable (ATAP 8.3). -/
theorem summable_norm_chebyshevSeries {a : ℕ → ℂ} {C ρ r : ℝ}
    (hρ : 1 < ρ) (hr : 1 < r) (hrρ : r < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    {z : ℂ} (hz : z ∈ bernsteinEllipse ⟨r, hr⟩) :
    Summable (fun n ↦ ‖a n * (T ℂ n).eval z‖) := by
  have hq0 : 0 ≤ r / ρ := by positivity
  have hq1 : r / ρ < 1 := (div_lt_one (by linarith : 0 < ρ)).2 hrρ
  exact ((summable_geometric_of_lt_one hq0 hq1).mul_left C).of_nonneg_of_le
    (fun n ↦ norm_nonneg _) (fun n ↦ term_norm_le hρ hr ha hz n)

/-- Geometric decay gives absolute convergence at each point of the open ellipse. -/
theorem summable_chebyshevSeries_of_geometric {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    {z : ℂ} (hz : z ∈ bernsteinEllipse ⟨ρ, hρ⟩) :
    Summable (fun n ↦ a n * (T ℂ n).eval z) := by
  obtain ⟨r, hr, hrρ, hzr⟩ := exists_smaller_bernsteinEllipse hρ hz
  exact (summable_norm_chebyshevSeries hρ hr hrρ ha hzr).of_norm

/-- Geometric coefficient bounds supply the classical series domain on an ellipse. -/
noncomputable def ComplexChebyshevSeriesPoint.ofGeometric {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    (z : bernsteinEllipse ⟨ρ, hρ⟩) : ComplexChebyshevSeriesPoint a :=
  .ofSummable (summable_chebyshevSeries_of_geometric hρ ha z.property)

@[simp] theorem ComplexChebyshevSeriesPoint.ofGeometric_val {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (z : bernsteinEllipse ⟨ρ, hρ⟩) :
    (ComplexChebyshevSeriesPoint.ofGeometric hρ ha z).val = z.val := rfl

/-- The Chebyshev extension is bounded on every strictly smaller ellipse. -/
theorem norm_complexChebyshevSeries_le {a : ℕ → ℂ} {C ρ r : ℝ}
    (hρ : 1 < ρ) (hr : 1 < r) (hrρ : r < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    {z : ComplexChebyshevSeriesPoint a} (hz : z.val ∈ bernsteinEllipse ⟨r, hr⟩) :
    ‖complexChebyshevSeries a z‖ ≤ C / (1 - r / ρ) := by
  have hs := summable_norm_chebyshevSeries hρ hr hrρ ha hz
  rw [complexChebyshevSeries_eq_tsum z hs.of_norm]
  have hq0 : 0 ≤ r / ρ := by positivity
  have hq1 : r / ρ < 1 := (div_lt_one (by linarith : 0 < ρ)).2 hrρ
  calc
    _ ≤ ∑' n, ‖a n * (T ℂ n).eval z.val‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, C * (r / ρ) ^ n := hs.tsum_le_tsum
      (fun n ↦ term_norm_le hρ hr ha hz n) ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]; ring

/-- Geometric coefficient decay defines an analytic function on the OPEN
Bernstein ellipse; boundedness on the whole ellipse is not required (ATAP 8.3). -/
theorem analyticOnNhd_chebyshev_tsum {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) :
    AnalyticOnNhd ℂ (fun z ↦ ∑' n : ℕ, a n * (T ℂ n).eval z) (bernsteinEllipse ⟨ρ, hρ⟩) := by
  intro z hz
  obtain ⟨r, hr, hrρ, hzr⟩ := exists_smaller_bernsteinEllipse hρ hz
  have hq0 : 0 ≤ r / ρ := by positivity
  have hq1 : r / ρ < 1 := (div_lt_one (by linarith : 0 < ρ)).2 hrρ
  have hd := differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
    (F := fun n z ↦ a n * (T ℂ n).eval z)
    (fun n ↦ ((T ℂ n).differentiable.const_mul (a n)).differentiableOn)
    (isOpen_bernsteinEllipse ⟨r, hr⟩) (fun n w hw ↦ term_norm_le hρ hr ha hw n)
  exact hd.analyticOnNhd (isOpen_bernsteinEllipse ⟨r, hr⟩) z hzr

/-- Geometric Chebyshev data are analytic on their typed open ellipse. -/
theorem analyticOnOpen_complexChebyshevSeries {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) :
    AnalyticOnOpen ⟨bernsteinEllipse ⟨ρ, hρ⟩, isOpen_bernsteinEllipse ⟨ρ, hρ⟩⟩
      (fun z ↦ complexChebyshevSeries a (ComplexChebyshevSeriesPoint.ofGeometric hρ ha z)) := by
  apply (analyticOnOpen_iff _ _ (fun z ↦ ∑' n : ℕ, a n * (T ℂ n).eval z) ?_).2
    (analyticOnNhd_chebyshev_tsum hρ ha)
  intro z
  have hz : z.val ∈ bernsteinEllipse ⟨ρ, hρ⟩ := z.property
  have hs := summable_chebyshevSeries_of_geometric hρ ha (z := z.val) hz
  exact (complexChebyshevSeries_eq_tsum
    (ComplexChebyshevSeriesPoint.ofGeometric hρ ha ⟨z.val, hz⟩)
    (by simpa only [ComplexChebyshevSeriesPoint.ofGeometric_val] using hs)).symm

/-- For continuous interval data, geometric decay of the existing integral
coefficients gives an analytic extension agreeing at every interval point. -/
theorem exists_analytic_extension_of_coefficient_decay {f : ℝ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (hf : ContinuousOn f (Icc (-1) 1))
    (ha : ∀ n, ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n))‖ ≤ C / ρ ^ n) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩) ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, F x = f x := by
  refine ⟨(fun z ↦ ∑' n : ℕ, complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n) * (T ℂ n).eval z),
    analyticOnNhd_chebyshev_tsum hρ ha, ?_⟩
  have hq0 : 0 ≤ ρ⁻¹ := by positivity
  have hq1 : ρ⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < ρ)).2 hρ
  have hs : Summable (fun n ↦ ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n))‖) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left C).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun n ↦ by simpa only [inv_pow, div_eq_mul_inv] using ha n)
  intro x hx
  have h := (hasSum_complexCoefficient_mul_eval_T hf hs hx).tsum_eq
  simpa only [complex_ofReal_eval_T] using h

end Polynomial.Chebyshev
