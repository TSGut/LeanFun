/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClassicalIntegration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # The classical domain of a Chebyshev coefficient
A coefficient at index n exists whenever f T_n is integrable. This domain is
larger than L¹ for a fixed positive index. Reference: ATAP Chapter 3.
-/
@[expose] public noncomputable section
open MeasureTheory Real Set
namespace Polynomial.Chebyshev

/-- Internal transport of integrability without rewriting a dependent representative. -/
theorem integrable_classicalMeasureT_iff_measureT (f : ℝ → ℝ) :
    Integrable f classicalMeasureT ↔ Integrable f measureT := by
  rw [classicalMeasureT_eq]

/-- Pointwise inputs with an integrable nth coefficient integrand (ATAP Ch. 3). -/
abbrev CoefficientInput (n : ℕ) :=
  {f : ℝ → ℝ // Integrable (fun x ↦ f x * (T ℝ n).eval x) classicalMeasureT}

/-- The defining coefficient integrand is integrable. -/
theorem CoefficientInput.integrable {n : ℕ} (f : CoefficientInput n) :
    Integrable (fun x ↦ f.val x * (T ℝ n).eval x) classicalMeasureT := f.property

/-- An L¹ function supplies an input at every index (ATAP Ch. 3). -/
def CoefficientInput.ofL1 (f : IntegrableInput classicalMeasureT) (n : ℕ) : CoefficientInput n :=
  ⟨f.val, integrable_classicalMeasureT_mul_T f n⟩

/-- A continuous function on the approximation interval supplies every index. -/
def CoefficientInput.ofContinuousOn (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (n : ℕ) : CoefficientInput n :=
  ofL1 ⟨f, integrable_classicalMeasureT hf⟩ n

/-- L¹ constructors preserve the pointwise input. -/
@[simp] theorem CoefficientInput.ofL1_val (f : IntegrableInput classicalMeasureT) (n : ℕ) :
    (ofL1 f n).val = f.val := rfl

/-- Continuous-input constructors preserve the pointwise input. -/
@[simp] theorem CoefficientInput.ofContinuousOn_val (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (n : ℕ) :
    (ofContinuousOn f hf n).val = f := rfl

/-- Finite linear combinations preserve the fixed-index domain. -/
def CoefficientInput.add {n : ℕ} (f g : CoefficientInput n) : CoefficientInput n :=
  ⟨fun x ↦ f.val x + g.val x, by simpa only [add_mul] using f.property.fun_add g.property⟩

/-- Scalar multiplication preserves the fixed-index domain. -/
def CoefficientInput.constMul {n : ℕ} (c : ℝ) (f : CoefficientInput n) : CoefficientInput n :=
  ⟨fun x ↦ c * f.val x, by simpa only [mul_assoc] using f.property.const_mul c⟩

/-- The zero-index domain is exactly L¹ (ATAP Ch. 3). -/
theorem coefficientInput_zero_iff (f : ℝ → ℝ) :
    Integrable (fun x ↦ f x * (T ℝ (0 : ℕ)).eval x) classicalMeasureT ↔
      Integrable f classicalMeasureT := by simp

/-- Fixed-index input membership depends only on the measure class. -/
theorem coefficientInput_congr_ae {n : ℕ} {f g : ℝ → ℝ}
    (h : f =ᵐ[classicalMeasureT] g) :
    Integrable (fun x ↦ f x * (T ℝ n).eval x) classicalMeasureT ↔
      Integrable (fun x ↦ g x * (T ℝ n).eval x) classicalMeasureT :=
  integrable_congr (h.mul (Filter.EventuallyEq.rfl))


/-- Integrable cosine pullbacks give integrable first-kind inputs (ATAP Ch. 3). -/
theorem integrable_classicalMeasureT_of_cos {f : ℝ → ℝ}
    (hf : IntervalIntegrable (fun θ ↦ f (Real.cos θ)) volume 0 Real.pi) :
    Integrable f classicalMeasureT := by
  have hc := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
    (a := (-1 : ℝ)) (b := 1) (f := arccos)
    (f' := fun x ↦ -(1 / √(1-x^2))) (g := fun θ ↦ f (cos θ))
    continuous_arccos.continuousOn
    (by
      intro x hx
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := by simpa using hx
      exact hasDerivAt_arccos hx'.1.ne' hx'.2.ne)
    (by intro x hx; simp)
  have hd := hc.mpr (by simpa using hf.symm)
  have hi : IntervalIntegrable (fun x ↦ f x * (Real.sqrt (1-x^2))⁻¹)
      volume (-1) 1 := by
    apply hd.neg.congr_uIoo
    intro x hx
    have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa using hx
    simp [Real.cos_arccos hx'.1.le hx'.2.le]
  rw [integrable_classicalMeasureT_iff]
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc] at hi
  have hs := (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).1 hi
  convert hs using 1
  ext x
  rw [(weightUT_apply x).2]
  exact mul_comm _ _

/-- Continuous cosine pullbacks suffice; no exterior values are used (ATAP Ch. 3). -/
theorem integrable_classicalMeasureT_of_continuous_cos {f : ℝ → ℝ}
    (hf : ContinuousOn (fun θ ↦ f (Real.cos θ)) (Set.Icc 0 Real.pi)) :
    Integrable f classicalMeasureT :=
  integrable_classicalMeasureT_of_cos (hf.intervalIntegrable_of_Icc Real.pi_pos.le)

end Polynomial.Chebyshev
