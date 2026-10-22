/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.MeasureTheory.Integral.ClassicalWeight
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import all Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-! # Classical Chebyshev weighted integration
Reference: DLMF Table 18.3.1. Both densities are evaluated only in (-1,1).
-/
@[expose] public noncomputable section
open MeasureTheory Set Real
open scoped NNReal ENNReal
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial.Chebyshev

/-- The second-kind density on its classical domain. -/
def weightU : C(Ioo (-1 : ℝ) 1, ℝ≥0) where
  toFun x := ⟨√(1 - (x : ℝ) ^ 2), sqrt_nonneg _⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop

/-- The first-kind density on its classical domain. -/
def weightT : C(Ioo (-1 : ℝ) 1, ℝ≥0) where
  toFun x := ⟨(√(1 - (x : ℝ) ^ 2))⁻¹, inv_nonneg.mpr (sqrt_nonneg _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.inv₀ (by fun_prop)
    intro x
    apply (sqrt_pos.2 ?_).ne'
    nlinarith [x.property.1, x.property.2, sq_nonneg ((x : ℝ) + 1)]

/-- The second-kind measure obtained from the subtype density. -/
def measureU : Measure ℝ := openIntervalWeightMeasure (-1) 1 weightU

/-- The first-kind measure obtained from the subtype density. -/
def classicalMeasureT : Measure ℝ := openIntervalWeightMeasure (-1) 1 weightT

/-- Internal compatibility with the existing first-kind measure. -/
theorem classicalMeasureT_eq : classicalMeasureT = measureT := by
  rw [measureT, restrict_withDensity measurableSet_Ioc, ← restrict_Ioo_eq_restrict_Ioc]
  apply openIntervalWeightMeasure_eq _ _ _ _ (by fun_prop)
  intro x
  simp only [weightT, sqrt_inv]
  rfl

/-- Characterization of the two classical densities. -/
theorem weightUT_apply (x : Ioo (-1 : ℝ) 1) :
    (weightU x : ℝ) = √(1 - (x : ℝ) ^ 2) ∧
      (weightT x : ℝ) = (√(1 - (x : ℝ) ^ 2))⁻¹ := ⟨rfl, rfl⟩

/-- Integrability against the second-kind density. -/
theorem integrable_measureU_iff (f : ℝ → ℝ) :
    Integrable f measureU ↔
      Integrable (fun x : Ioo (-1 : ℝ) 1 ↦ (weightU x : ℝ) * f x) volume :=
  integrable_openIntervalWeightMeasure_iff _ _ _ _

/-- Integrability against the first-kind density. -/
theorem integrable_classicalMeasureT_iff (f : ℝ → ℝ) :
    Integrable f classicalMeasureT ↔
      Integrable (fun x : Ioo (-1 : ℝ) 1 ↦ (weightT x : ℝ) * f x) volume :=
  integrable_openIntervalWeightMeasure_iff _ _ _ _

/-- The classical second-kind integral formula for an integrable input. -/
theorem integral_measureU (f : IntegrableInput measureU) :
    ∫ x, f.val x ∂measureU =
      ∫ x : Ioo (-1 : ℝ) 1, f.val x * (weightU x : ℝ) := by
  exact (integral_openIntervalWeightMeasure _ _ _ f).trans
    (integral_congr_ae (Filter.Eventually.of_forall (fun _ ↦ mul_comm _ _)))

/-- Internal pointwise density comparison. -/
theorem weightU_eq_weightT_mul (x : Ioo (-1 : ℝ) 1) :
    (weightU x : ℝ) = (weightT x : ℝ) * (1 - (x : ℝ) ^ 2) := by
  have h : 0 < 1 - (x : ℝ) ^ 2 := by nlinarith [x.property.1, x.property.2]
  change √(1 - (x : ℝ) ^ 2) = (√(1 - (x : ℝ) ^ 2))⁻¹ * _
  field_simp [(sqrt_pos.2 h).ne']
  exact sq_sqrt h.le

/-- Comparison of weights preserves integrability as well as the integral value. -/
theorem integral_measureU_eq_classicalMeasureT
    (f : IntegrableInput measureU) :
    Integrable (fun x ↦ f.val x * (1 - x ^ 2)) classicalMeasureT ∧
      (∫ x, f.val x ∂measureU) =
        ∫ x, f.val x * (1 - x ^ 2) ∂classicalMeasureT := by
  have h : Integrable (fun x ↦ f.val x * (1 - x ^ 2)) classicalMeasureT := by
    rw [integrable_classicalMeasureT_iff]
    convert (integrable_measureU_iff _).1 f.property using 1
    ext x
    rw [weightU_eq_weightT_mul]
    ring
  refine ⟨h, ?_⟩
  rw [integral_measureU]
  have he := integral_openIntervalWeightMeasure (-1) 1 weightT
    (⟨_, h⟩ : IntegrableInput classicalMeasureT)
  apply Eq.trans _ he.symm
  apply integral_congr_ae
  filter_upwards [] with x
  rw [weightU_eq_weightT_mul]
  ring

end Polynomial.Chebyshev
