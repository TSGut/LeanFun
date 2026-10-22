/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.AnalyticConverse

/-! # Characterizing analytic Chebyshev data
Analyticity on an open ellipse is equivalent to geometric coefficient bounds
at every strictly smaller radius. Reference: ATAP, Theorems 8.1--8.3.
-/

public section
namespace Polynomial.Chebyshev
open Complex Set

/-- Continuous interval data with equal values have equal complex Chebyshev
coefficients (ATAP, Chapter 3). -/
theorem complexCoefficient_congr_of_continuousOn {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1)) (hg : ContinuousOn g (Icc (-1) 1))
    (hfg : EqOn f g (Icc (-1) 1)) (n : ℕ) :
    (complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n)) = (complexCoefficient (ComplexCoefficientInput.ofContinuousOn g hg n)) := by
  apply Complex.ext
  · rw [complexCoefficient_re hf, complexCoefficient_re hg]
    exact coefficient_congr (fun x hx ↦ congrArg Complex.re (hfg hx))
  · rw [complexCoefficient_im hf, complexCoefficient_im hg]
    exact coefficient_congr (fun x hx ↦ congrArg Complex.im (hfg hx))

/-- An analytic extension gives geometric coefficient bounds on all smaller
ellipses, without assuming boundedness on the original ellipse (ATAP 8.1). -/
theorem coefficient_decay_of_analytic_extension {f : ℝ → ℂ} {F : ℂ → ℂ} {ρ r : ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) (hr : 1 < r) (hrρ : r < ρ)
    (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hr.trans hrρ⟩))
    (hagree : ∀ x ∈ Icc (-1 : ℝ) 1, F x = f x) :
    ∃ C : ℝ, ∀ n, ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n))‖ ≤ C / r ^ n := by
  have hsub := closure_bernsteinEllipse_subset hr hrρ
  obtain ⟨M, hM⟩ := (isCompact_closure_bernsteinEllipse ⟨r, hr⟩).bddAbove_image
    (hF.continuousOn.mono hsub).norm
  have hb : ∀ z ∈ bernsteinEllipse ⟨r, hr⟩, ‖F z‖ ≤ max M 0 := fun z hz ↦
    (hM ⟨z, subset_closure hz, rfl⟩).trans (le_max_left _ _)
  have hFr := hF.mono (subset_closure.trans hsub)
  have hcont : ContinuousOn (fun x : ℝ ↦ F x) (Icc (-1) 1) :=
    hFr.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun x hx ↦ ofReal_mem_bernsteinEllipse hr hx)
  refine ⟨2 * max M 0, fun n ↦ ?_⟩
  rw [complexCoefficient_congr_of_continuousOn hf hcont (fun x hx ↦ (hagree x hx).symm)]
  apply (norm_complexCoefficient_le_of_analytic hr hFr hb n).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (by split_ifs <;> norm_num) (le_max_right _ _)

/-- Analytic extension to an open ellipse is equivalent to decay at every
strictly smaller geometric rate. A bound at the outer radius is not asserted
(ATAP, Theorems 8.1--8.3). -/
theorem exists_analytic_extension_iff_coefficient_decay {f : ℝ → ℂ} {ρ : ℝ}
    (hρ : 1 < ρ) (hf : ContinuousOn f (Icc (-1) 1)) :
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩) ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, F x = f x) ↔
    ∀ r : ℝ, 1 < r → r < ρ → ∃ C : ℝ, ∀ n, ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n))‖ ≤ C / r ^ n := by
  constructor
  · rintro ⟨F, hF, heq⟩ r hr hrρ
    exact coefficient_decay_of_analytic_extension hf hr hrρ hF heq
  · intro ha
    refine ⟨(fun z ↦ ∑' n : ℕ, complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n) * (T ℂ n).eval z), ?_, ?_⟩
    · intro z hz
      obtain ⟨r, hr, hrρ, hzr⟩ := exists_smaller_bernsteinEllipse hρ hz
      obtain ⟨C, hC⟩ := ha r hr hrρ
      exact analyticOnNhd_chebyshev_tsum hr hC z hzr
    · obtain ⟨r, hr, hrρ⟩ := exists_between hρ
      obtain ⟨C, hC⟩ := ha r hr hrρ
      have hq0 : 0 ≤ r⁻¹ := by positivity
      have hq1 : r⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < r)).2 hr
      have hs : Summable (fun n ↦ ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n))‖) :=
        Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (fun n ↦ by simpa only [inv_pow, div_eq_mul_inv] using hC n)
          ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
      intro x hx
      simpa only [complex_ofReal_eval_T] using
        (hasSum_complexCoefficient_mul_eval_T hf hs hx).tsum_eq

end Polynomial.Chebyshev
