/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClassicalMeasure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Polynomial

/-! # Classical first-kind Chebyshev integration
The cosine substitution preserves integrability, including integrable endpoint
singularities. References: DLMF Table 18.3.1; ATAP Chapters 3 and 8.
-/
@[expose] public noncomputable section
open MeasureTheory Real Set
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial.Chebyshev

/-- Continuous inputs are integrable for the first-kind measure (DLMF 18.3). -/
theorem integrable_classicalMeasureT {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) : Integrable f classicalMeasureT := by
  rw [classicalMeasureT_eq]
  exact integrable_measureT hf

/-- The subtype density formula for an integrable first-kind input (DLMF 18.3). -/
theorem integral_classicalMeasureT (f : IntegrableInput classicalMeasureT) :
    ∫ x, f.val x ∂classicalMeasureT =
      ∫ x : Ioo (-1 : ℝ) 1, (weightT x : ℝ) * f.val x :=
  integral_openIntervalWeightMeasure (-1) 1 weightT f

/-- Cosine substitution preserves every integrable first-kind input (ATAP Ch. 3). -/
theorem intervalIntegrable_classicalMeasureT_cos (f : IntegrableInput classicalMeasureT) :
    IntervalIntegrable (fun θ ↦ f.val (cos θ)) volume 0 π := by
  have hs := (integrable_classicalMeasureT_iff f.val).1 f.property
  have hi : IntervalIntegrable (fun x : ℝ ↦ f.val x * (√(1-x^2))⁻¹)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff, uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc]
    apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).2
    change Integrable (fun x : Ioo (-1 : ℝ) 1 ↦ f.val x * (√(1-(x:ℝ)^2))⁻¹) volume
    convert hs using 1
    ext x
    rw [(weightUT_apply x).2]
    exact mul_comm _ _
  have hc := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
    (a := (-1 : ℝ)) (b := 1) (f := arccos)
    (f' := fun x ↦ -(1 / √(1-x^2))) (g := fun θ ↦ f.val (cos θ))
    continuous_arccos.continuousOn
    (by
      intro x hx
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := by simpa using hx
      exact hasDerivAt_arccos hx'.1.ne' hx'.2.ne)
    (by intro x hx; simp)
  have hd : IntervalIntegrable
      (fun x ↦ ((fun θ ↦ f.val (cos θ)) ∘ arccos) x * -(1 / √(1-x^2)))
      volume (-1) 1 := by
    apply hi.neg.congr_uIoo
    intro x hx
    simp only [uIoo_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    simp [cos_arccos hx.1.le hx.2.le]
  simpa only [arccos_neg_one, arccos_one] using (hc.mp hd).symm

/-- Cosine integration with a finite classical value on both sides (ATAP Ch. 3). -/
theorem integral_classicalMeasureT_eq_integral_cos (f : IntegrableInput classicalMeasureT) :
    ∫ x, f.val x ∂classicalMeasureT = ∫ θ in 0..π, f.val (cos θ) := by
  simpa only [classicalMeasureT_eq] using
    (integral_measureT_eq_integral_cos (f := f.val))

/-- Every coefficient integrand of an L¹ input is integrable (ATAP Ch. 3). -/
theorem integrable_classicalMeasureT_mul_T (f : IntegrableInput classicalMeasureT) (n : ℤ) :
    Integrable (fun x ↦ f.val x * (T ℝ n).eval x) classicalMeasureT := by
  rw [integrable_classicalMeasureT_iff]
  have hf := (integrable_classicalMeasureT_iff f.val).1 f.property
  have h := hf.mul_bdd
    (show AEStronglyMeasurable (fun x : Ioo (-1 : ℝ) 1 ↦ (T ℝ n).eval (x : ℝ)) volume from
      (by fun_prop : Continuous (fun x : Ioo (-1 : ℝ) 1 ↦ (T ℝ n).eval (x : ℝ))).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x : Ioo (-1 : ℝ) 1 ↦
      show ‖(T ℝ n).eval (x : ℝ)‖ ≤ 1 from by
        rw [Real.norm_eq_abs]
        exact abs_eval_T_real_le_one n (abs_le.mpr ⟨x.property.1.le, x.property.2.le⟩)))
  simpa only [mul_assoc] using h

/-- First-kind moments, with integrability, for all integer indices (DLMF 18.3). -/
theorem classicalMeasureT_moments (n : ℤ) :
    Integrable (fun x ↦ (T ℝ n).eval x) classicalMeasureT ∧
      (∫ x, (T ℝ n).eval x ∂classicalMeasureT) = if n = 0 then π else 0 := by
  refine ⟨integrable_classicalMeasureT (by fun_prop), ?_⟩
  rw [classicalMeasureT_eq]
  split_ifs with h
  · subst n; exact integral_eval_T_real_measureT_zero
  · exact integral_eval_T_real_measureT_of_ne_zero h

/-- First-kind orthogonality and squared norms, with integrability (DLMF 18.3). -/
theorem classicalMeasureT_orthogonality (n m : ℕ) :
    Integrable (fun x ↦ (T ℝ n).eval x * (T ℝ m).eval x) classicalMeasureT ∧
      (∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂classicalMeasureT) =
        if n = m then (if n = 0 then π else π / 2) else 0 := by
  refine ⟨integrable_classicalMeasureT (by fun_prop), ?_⟩
  rw [classicalMeasureT_eq]
  split_ifs with h hn
  · subst m; subst n; exact integral_eval_T_real_mul_self_measureT_zero
  · subst m; exact integral_T_real_mul_self_measureT_of_ne_zero hn
  · exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne h

end Polynomial.Chebyshev
