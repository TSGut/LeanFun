/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Coefficients
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Polynomial

/-! # Classical inputs for complex Chebyshev coefficients
The domain at index n consists exactly of integrable products f T_n.
Reference: ATAP, Chapters 3 and 8.
-/

@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open MeasureTheory Real Set

/-- Complex integrability can be reconstructed from real and imaginary parts. -/
theorem integrable_complex_of_re_im {f : ℝ → ℂ} {μ : Measure ℝ}
    (hr : Integrable (fun x ↦ (f x).re) μ)
    (hi : Integrable (fun x ↦ (f x).im) μ) : Integrable f μ := by
  convert hr.ofReal.fun_add (hi.ofReal.mul_const Complex.I) using 1
  funext x
  exact (Complex.re_add_im (f x)).symm

/-- Continuous complex data are integrable for the first-kind measure (ATAP Ch. 3). -/
theorem integrable_classicalMeasureT_complex {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1)) : Integrable f classicalMeasureT :=
  integrable_complex_of_re_im
    (integrable_classicalMeasureT (Complex.continuous_re.comp_continuousOn hf))
    (integrable_classicalMeasureT (Complex.continuous_im.comp_continuousOn hf))

/-- Complex integrable inputs retain pointwise representatives (ATAP Ch. 3). -/
abbrev ComplexIntegrableInput := {f : ℝ → ℂ // Integrable f classicalMeasureT}

/-- A complex L1 input has a genuine finite integral. -/
theorem ComplexIntegrableInput.integrable (f : ComplexIntegrableInput) :
    Integrable f.val classicalMeasureT := f.property

/-- The complex nth coefficient exists exactly on this integrable-product domain. -/
abbrev ComplexCoefficientInput (n : ℕ) :=
  {f : ℝ → ℂ // Integrable (fun x ↦ f x * (((T ℝ n).eval x : ℝ) : ℂ)) classicalMeasureT}

/-- The defining complex coefficient integrand is integrable. -/
theorem ComplexCoefficientInput.integrable {n : ℕ} (f : ComplexCoefficientInput n) :
    Integrable (fun x ↦ f.val x * (((T ℝ n).eval x : ℝ) : ℂ)) classicalMeasureT := f.property

/-- L1 data supply the complex input at every index (ATAP Ch. 3). -/
def ComplexCoefficientInput.ofL1 (f : ComplexIntegrableInput) (n : ℕ) :
    ComplexCoefficientInput n := by
  refine ⟨f.val, integrable_complex_of_re_im ?_ ?_⟩
  · simpa using integrable_classicalMeasureT_mul_T ⟨_, f.property.re⟩ n
  · simpa using integrable_classicalMeasureT_mul_T ⟨_, f.property.im⟩ n

/-- Continuous interval data supply every complex coefficient. -/
def ComplexCoefficientInput.ofContinuousOn (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc (-1) 1)) (n : ℕ) : ComplexCoefficientInput n :=
  ofL1 ⟨f, integrable_classicalMeasureT_complex hf⟩ n

/-- A real coefficient input also supplies the corresponding complex input. -/
def ComplexCoefficientInput.ofReal {n : ℕ} (f : CoefficientInput n) :
    ComplexCoefficientInput n :=
  ⟨fun x ↦ (f.val x : ℂ), by simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul] using (f.property.ofReal (𝕜 := ℂ))⟩

/-- Real parts retain the full fixed-index domain. -/
def ComplexCoefficientInput.re {n : ℕ} (f : ComplexCoefficientInput n) : CoefficientInput n :=
  ⟨fun x ↦ (f.val x).re, by simpa using f.property.re⟩

/-- Imaginary parts retain the full fixed-index domain. -/
def ComplexCoefficientInput.im {n : ℕ} (f : ComplexCoefficientInput n) : CoefficientInput n :=
  ⟨fun x ↦ (f.val x).im, by simpa using f.property.im⟩

@[simp] theorem ComplexCoefficientInput.ofL1_val (f : ComplexIntegrableInput) (n : ℕ) :
    (ofL1 f n).val = f.val := rfl

@[simp] theorem ComplexCoefficientInput.ofContinuousOn_val (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc (-1) 1)) (n : ℕ) :
    (ofContinuousOn f hf n).val = f := rfl

@[simp] theorem ComplexCoefficientInput.ofReal_val {n : ℕ} (f : CoefficientInput n) :
    (ofReal f).val = fun x ↦ (f.val x : ℂ) := rfl

@[simp] theorem ComplexCoefficientInput.re_val {n : ℕ} (f : ComplexCoefficientInput n) :
    f.re.val = fun x ↦ (f.val x).re := rfl

@[simp] theorem ComplexCoefficientInput.im_val {n : ℕ} (f : ComplexCoefficientInput n) :
    f.im.val = fun x ↦ (f.val x).im := rfl

/-- The complex zero-index domain is precisely L1. -/
theorem complexCoefficientInput_zero_iff (f : ℝ → ℂ) :
    Integrable (fun x ↦ f x * (((T ℝ (0 : ℕ)).eval x : ℝ) : ℂ)) classicalMeasureT ↔
      Integrable f classicalMeasureT := by simp

end Polynomial.Chebyshev
