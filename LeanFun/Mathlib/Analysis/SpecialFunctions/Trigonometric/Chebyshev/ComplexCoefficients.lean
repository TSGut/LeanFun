/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexCoefficientInput
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Complex Chebyshev coefficients

The weighted-integral definition with the full constant coefficient convention,
compatible with real coefficients. Reference: ATAP, Chapters 3 and 8.
-/


public section

namespace Polynomial.Chebyshev

open Real MeasureTheory

/-- Complex Chebyshev coefficients on their full fixed-index classical domain
(ATAP, Chapter 3), with the full constant term. -/
@[expose] noncomputable def complexCoefficient {n : ℕ} (f : ComplexCoefficientInput n) : ℂ :=
  ((if n = 0 then 1 else 2 : ℝ) / π : ℝ) *
    ∫ x, f.val x * (((T ℝ n).eval x : ℝ) : ℂ) ∂classicalMeasureT

/-- The classical weighted-integral formula (ATAP, Chapter 3). -/
theorem complexCoefficient_apply {n : ℕ} (f : ComplexCoefficientInput n) :
    complexCoefficient f = ((if n = 0 then 1 else 2 : ℝ) / π : ℝ) *
      ∫ x, f.val x * (((T ℝ n).eval x : ℝ) : ℂ) ∂classicalMeasureT := rfl

/-- Internal bridge to the imported first-kind measure. -/
theorem complexCoefficient_eq_integral {n : ℕ} (f : ComplexCoefficientInput n) :
    complexCoefficient f = ((if n = 0 then 1 else 2 : ℝ) / π : ℝ) *
      ∫ x, f.val x * (((T ℝ n).eval x : ℝ) : ℂ) ∂measureT := by
  unfold complexCoefficient
  exact congrArg (fun μ ↦ ((if n = 0 then 1 else 2 : ℝ) / π : ℝ) *
    ∫ x, f.val x * (((T ℝ n).eval x : ℝ) : ℂ) ∂μ) classicalMeasureT_eq

/-- The complex definition extends the real weighted-integral coefficient (ATAP, Chapter 3). -/
@[simp] theorem complexCoefficient_ofReal {n : ℕ} (f : CoefficientInput n) :
    complexCoefficient (ComplexCoefficientInput.ofReal f) = ((coefficient f) : ℂ) := by
  rw [complexCoefficient, coefficient]
  simp only [ComplexCoefficientInput.ofReal_val, ← Complex.ofReal_mul,
    _root_.integral_complex_ofReal]

/-- Continuous complex functions are integrable for the Chebyshev weight
(DLMF Table 18.3.1). -/
theorem integrable_measureT_complex {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1) 1)) : Integrable f measureT := by
  have hr : Integrable (fun x ↦ ((f x).re : ℂ)) measureT := (integrable_measureT (Complex.continuous_re.comp_continuousOn hf)).ofReal
  have hi : Integrable (fun x ↦ ((f x).im : ℂ)) measureT := (integrable_measureT (Complex.continuous_im.comp_continuousOn hf)).ofReal
  convert hr.add (hi.mul_const Complex.I) using 1
  funext x
  exact (Complex.re_add_im (f x)).symm

/-- The weighted complex integral has the same cosine change of variables as the
real integral (ATAP, Chapter 3). -/
theorem integral_measureT_complex_eq_integral_cos {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    ∫ x, f x ∂measureT = ∫ θ in 0..π, f (cos θ) := by
  have hc : ContinuousOn (fun θ ↦ f (cos θ)) (Set.uIcc 0 π) := by
    exact hf.comp continuous_cos.continuousOn (fun θ _ ↦ ⟨neg_one_le_cos θ, cos_le_one θ⟩)
  have hr' : IntervalIntegrable (fun θ ↦ ((f (cos θ)).re : ℂ)) volume 0 π :=
    (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hc)).intervalIntegrable
  have hi' : IntervalIntegrable (fun θ ↦ ((f (cos θ)).im : ℂ)) volume 0 π :=
    (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn hc)).intervalIntegrable
  calc
    _ = (∫ x, (f x).re ∂measureT : ℝ) +
        (∫ x, (f x).im ∂measureT : ℝ) * Complex.I := by
      simpa only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex, RCLike.ofReal_eq_complex_ofReal,
        _root_.integral_complex_ofReal] using (integral_coe_re_add_coe_im (integrable_measureT_complex hf)).symm
    _ = (∫ θ in 0..π, (f (cos θ)).re : ℝ) +
        (∫ θ in 0..π, (f (cos θ)).im : ℝ) * Complex.I := by
      rw [integral_measureT_eq_integral_cos, integral_measureT_eq_integral_cos]
    _ = _ := by
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal,
        ← intervalIntegral.integral_mul_const,
        ← intervalIntegral.integral_add hr' (hi'.mul_const Complex.I)]
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact Complex.re_add_im (f (cos θ))

/-- Cosine representation of complex coefficients (ATAP, Chapter 3). -/
theorem complexCoefficient_eq_integral_cos {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (n : ℕ) :
    complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n) = ((if n = 0 then 1 else 2 : ℝ) / π : ℝ) *
      ∫ θ in 0..π, f (cos θ) * (cos (n * θ) : ℂ) := by
  rw [complexCoefficient_eq_integral, ComplexCoefficientInput.ofContinuousOn_val, integral_measureT_complex_eq_integral_cos
    (f := fun x ↦ f x * (((T ℝ n).eval x : ℝ) : ℂ)) (hf.mul (by fun_prop))]
  simp only [T_real_cos, Int.cast_natCast]

/-- Real and imaginary parts commute with Chebyshev coefficients (ATAP, Chapter 3). -/
theorem complexCoefficient_re {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (n : ℕ) :
    (complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n)).re = (coefficient (n := n) ⟨(fun x ↦ (f x).re), by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) := by
  have hi := integrable_measureT_complex (hf.mul (by fun_prop : ContinuousOn
    (fun x : ℝ ↦ (((T ℝ n).eval x : ℝ) : ℂ)) (Set.Icc (-1) 1)))
  have hr := integral_re hi
  change (∫ x, (f x * (((T ℝ n).eval x : ℝ) : ℂ)).re ∂measureT) =
    (∫ x, f x * (((T ℝ n).eval x : ℝ) : ℂ) ∂measureT).re at hr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hr
  rw [complexCoefficient_eq_integral, ComplexCoefficientInput.ofContinuousOn_val]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← hr]
  by_cases hn : n = 0
  · subst n
    simp [coefficient_zero, div_eq_mul_inv, mul_comm]
  · rw [coefficient_of_ne_zero _ hn]
    simp only [hn, ite_eq_right, not_false_eq_true]

/-- Imaginary parts commute with Chebyshev coefficients (ATAP, Chapter 3). -/
theorem complexCoefficient_im {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (n : ℕ) :
    (complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf n)).im = (coefficient (n := n) ⟨(fun x ↦ (f x).im), by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) := by
  have hi := integrable_measureT_complex (hf.mul (by fun_prop : ContinuousOn
    (fun x : ℝ ↦ (((T ℝ n).eval x : ℝ) : ℂ)) (Set.Icc (-1) 1)))
  have hr := integral_im hi
  change (∫ x, (f x * (((T ℝ n).eval x : ℝ) : ℂ)).im ∂measureT) =
    (∫ x, f x * (((T ℝ n).eval x : ℝ) : ℂ) ∂measureT).im at hr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at hr
  rw [complexCoefficient_eq_integral, ComplexCoefficientInput.ofContinuousOn_val]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, ← hr]
  by_cases hn : n = 0
  · subst n
    simp [coefficient_zero, div_eq_mul_inv, mul_comm]
  · rw [coefficient_of_ne_zero _ hn]
    simp only [hn, ite_eq_right, not_false_eq_true]

end Polynomial.Chebyshev
