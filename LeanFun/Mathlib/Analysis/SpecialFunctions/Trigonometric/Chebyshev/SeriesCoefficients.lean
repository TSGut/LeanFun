/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.SeriesCalculus
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.AnalyticConverse
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexCoefficientBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! # Recovering coefficients from absolutely convergent Chebyshev series
This identifies the coefficients produced by infinite coefficient operations
with the existing integral definition. Reference: ATAP, Chapters 3 and 4.
-/

@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open Set Filter Real MeasureTheory

/-- Complex Chebyshev modes have norm at most one on the real interval. -/
theorem norm_eval_T_complex_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖(T ℂ n).eval (x : ℂ)‖ ≤ 1 := by
  rw [← complex_ofReal_eval_T, Complex.norm_real, Real.norm_eq_abs]
  exact abs_eval_T_real_le_one _ (abs_le.mpr hx)

/-- Absolute coefficient summability gives actual convergence on the closed interval. -/
theorem summable_chebyshevSeries_of_absolute {a : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (x : Icc (-1 : ℝ) 1) :
    Summable (fun n ↦ a n * (T ℂ n).eval (x.val : ℂ)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ ha
  intro n
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_T_complex_le_one n x.property)

/-- Absolute summability supplies convergent points, including both endpoints. -/
def ComplexChebyshevSeriesPoint.ofAbsolute {a : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (x : Icc (-1 : ℝ) 1) :
    ComplexChebyshevSeriesPoint a :=
  .ofSummable (summable_chebyshevSeries_of_absolute ha x)

@[simp] theorem ComplexChebyshevSeriesPoint.ofAbsolute_val {a : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (x : Icc (-1 : ℝ) 1) :
    (ComplexChebyshevSeriesPoint.ofAbsolute ha x).val = (x.val : ℂ) := rfl

/-- Absolute coefficient summability bounds the classical represented function. -/
theorem norm_complexChebyshevSeries_le_tsum {a : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (x : Icc (-1 : ℝ) 1) :
    ‖complexChebyshevSeries a (.ofAbsolute ha x)‖ ≤ ∑' n, ‖a n‖ := by
  have hb (n : ℕ) : ‖a n * (T ℂ n).eval (x.val : ℂ)‖ ≤ ‖a n‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_T_complex_le_one n x.property)
  have hs : Summable (fun n : ℕ ↦ ‖a n * (T ℂ n).eval (x.val : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb ha
  rw [complexChebyshevSeries_eq_tsum (ComplexChebyshevSeriesPoint.ofAbsolute ha x)
    (by simpa only [ComplexChebyshevSeriesPoint.ofAbsolute_val] using hs.of_norm)]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb ha)

/-- Absolute summability makes the classical sum continuous on its closed real interval. -/
theorem continuousOn_complexChebyshevSeries {a : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) :
    Continuous (fun x : Icc (-1 : ℝ) 1 ↦ complexChebyshevSeries a (.ofAbsolute ha x)) := by
  have h := tendstoUniformlyOn_tsum_nat ha (fun n (x : ℝ) hx ↦
    (show ‖a n * (T ℂ n).eval (x : ℂ)‖ ≤ ‖a n‖ by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_T_complex_le_one n hx)))
  have hc := h.continuousOn (Eventually.of_forall (fun N ↦ by fun_prop)).frequently
  have he : (fun x : Icc (-1 : ℝ) 1 ↦ complexChebyshevSeries a (.ofAbsolute ha x)) =
      (fun x : Icc (-1 : ℝ) 1 ↦ ∑' n, a n * (T ℂ n).eval (x.val : ℂ)) := by
    funext x
    exact complexChebyshevSeries_eq_tsum _ (summable_chebyshevSeries_of_absolute ha x)
  rw [he]
  exact hc.domRestrict

end Polynomial.Chebyshev

public section
namespace Polynomial.Chebyshev
open Set Filter Real MeasureTheory

/-- Recover the full-constant integral coefficients of an absolutely convergent
Chebyshev expansion. -/
private theorem complexCoefficient_complexChebyshevSeries_of_continuous_representative {a : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1))
    (he : ∀ x : Icc (-1 : ℝ) 1, f x.val = complexChebyshevSeries a (.ofAbsolute ha x))
    (k : ℕ) :
    (complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf k)) = a k := by
  let d : ℂ := (((if k = 0 then 1 else 2 : ℝ) / π : ℝ) : ℂ)
  have hb (n : ℕ) (θ : ℝ) :
      ‖a n * (T ℂ n).eval (cos θ : ℂ) * (cos (k * θ) : ℂ)‖ ≤ ‖a n‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (by positivity)
      (abs_cos_le_one _)).trans (mul_le_of_le_one_right (norm_nonneg _)
        (norm_eval_T_complex_le_one n ⟨neg_one_le_cos _, cos_le_one _⟩))
  have h := hasSum_integral_series
    (F := fun n θ ↦ a n * (T ℂ n).eval (cos θ : ℂ) * (cos (k * θ) : ℂ))
    (a := 0) (b := π) (fun n ↦ by fun_prop) ha (fun n θ _ ↦ hb n θ)
    (fun θ _ ↦ by
      have hs : Summable (fun n ↦ a n * (T ℂ n).eval (cos θ : ℂ)) := by
        apply Summable.of_norm
        apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ ha
        intro n
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (norm_eval_T_complex_le_one n ⟨neg_one_le_cos _, cos_le_one _⟩)
      have heq : (∑' n, a n * (T ℂ n).eval (cos θ : ℂ)) = f (cos θ) := by
        rw [he ⟨cos θ, neg_one_le_cos θ, cos_le_one θ⟩]
        exact (complexChebyshevSeries_eq_tsum
          (ComplexChebyshevSeriesPoint.ofAbsolute ha ⟨cos θ, neg_one_le_cos θ, cos_le_one θ⟩)
          (by simpa only [ComplexChebyshevSeriesPoint.ofAbsolute_val] using hs)).symm
      exact (heq ▸ hs.hasSum).mul_right (cos (k * θ) : ℂ))
  have hcoeff : HasSum (fun n ↦ if n = k then a n else 0)
      ((complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf k))) := by
    have hd := h.mul_left d
    rw [complexCoefficient_eq_integral_cos hf]
    convert hd using 1
    · ext n
      have he := complexCoefficient_eq_integral_cos
        (f := fun x : ℝ ↦ a n * (T ℂ n).eval (x : ℂ)) (by fun_prop) k
      rw [complexCoefficient_const_mul _ (by fun_prop), complexCoefficient_eval_T] at he
      simpa only [d, mul_ite, mul_one, mul_zero, mul_assoc] using he
  apply hcoeff.unique
  convert hasSum_ite_eq k (a k) using 1
  ext n
  split_ifs with hn <;> simp_all

end Polynomial.Chebyshev

public section
namespace Polynomial.Chebyshev
open Set

/-- Recovery uses the original indexed integrability domain and depends only on
agreement with the classical series on the interval. -/
theorem complexCoefficient_complexChebyshevSeries {a : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (k : ℕ) (f : ComplexCoefficientInput k)
    (he : ∀ x : Icc (-1 : ℝ) 1,
      f.val x.val = complexChebyshevSeries a (.ofAbsolute ha x)) :
    complexCoefficient f = a k := by
  have hf : ContinuousOn f.val (Icc (-1 : ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuousOn_complexChebyshevSeries ha).congr (fun x ↦ (he x).symm)
  have hi : ComplexCoefficientInput.ofContinuousOn f.val hf k = f := Subtype.ext rfl
  rw [← hi]
  exact complexCoefficient_complexChebyshevSeries_of_continuous_representative ha hf he k

end Polynomial.Chebyshev
