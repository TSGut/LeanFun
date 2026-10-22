/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClassicalMeasure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

import Mathlib.Topology.Algebra.Polynomial

/-!
# Orthogonality of second-kind Chebyshev polynomials

This extends Mathlib's first-kind orthogonality API using its existing `U` polynomials.
The product integral reduces to first-kind moments through the cosine substitution.

## References

* DLMF Table 18.3.1: https://dlmf.nist.gov/18.3
* DLMF 18.5.1--18.5.2: https://dlmf.nist.gov/18.5
-/

public section

namespace Polynomial.Chebyshev

open Real intervalIntegral MeasureTheory
open scoped NNReal

/-- Continuous functions are integrable for the second-kind weight (DLMF Table 18.3.1). -/
theorem integrable_measureU {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    Integrable f measureU := by
  have hi : IntervalIntegrable (fun x ↦ √(1 - x ^ 2) * f x) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact (by fun_prop : ContinuousOn (fun x : ℝ ↦ √(1 - x ^ 2)) _).mul hf)
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hi
  rw [integrable_measureU_iff]
  rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc] at hi
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).1 hi

/-- Product integral reduction to first-kind Chebyshev moments; DLMF Table 18.3.1
and the trigonometric representations in DLMF 18.5.1--18.5.2. -/
theorem integral_eval_U_real_mul_eval_U_real_measureU (n m : ℤ) :
    ∫ x, (U ℝ n).eval x * (U ℝ m).eval x ∂measureU =
      ((∫ x, (T ℝ (n - m)).eval x ∂classicalMeasureT) -
       (∫ x, (T ℝ (n + m + 2)).eval x ∂classicalMeasureT)) / 2 := by
  rw [classicalMeasureT_eq]
  have h := (integral_measureU_eq_classicalMeasureT
    ⟨fun x ↦ (U ℝ n).eval x * (U ℝ m).eval x, integrable_measureU (by fun_prop)⟩).2
  rw [classicalMeasureT_eq] at h
  rw [h]
  rw [← MeasureTheory.integral_sub (integrable_measureT (by fun_prop))
    (integrable_measureT (by fun_prop)), ← MeasureTheory.integral_div]
  rw [integral_measureT_eq_integral_cos, integral_measureT_eq_integral_cos]
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only [T_real_cos]
  have hn := U_real_cos (n := n) (θ := θ)
  have hm := U_real_cos (n := m) (θ := θ)
  have hs := Real.sin_sq_add_cos_sq θ
  have hp := Real.two_mul_sin_mul_sin (((n : ℝ) + 1) * θ) (((m : ℝ) + 1) * θ)
  have hsub : ((n : ℝ) + 1) * θ - ((m : ℝ) + 1) * θ = (n - m) * θ := by ring
  have hadd : ((n : ℝ) + 1) * θ + ((m : ℝ) + 1) * θ = (n + m + 2) * θ := by ring
  rw [hsub, hadd] at hp
  push_cast
  calc
    _ = ((U ℝ n).eval (cos θ) * sin θ) * ((U ℝ m).eval (cos θ) * sin θ) := by
      rw [show 1 - cos θ ^ 2 = sin θ ^ 2 by nlinarith [hs]]
      ring
    _ = sin (((n : ℝ) + 1) * θ) * sin (((m : ℝ) + 1) * θ) := by rw [hn, hm]
    _ = _ := by linarith [hp]

/-- Distinct second-kind Chebyshev polynomials are orthogonal (DLMF Table 18.3.1). -/
theorem integral_eval_U_real_mul_eval_U_real_measureU_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x, (U ℝ n).eval x * (U ℝ m).eval x ∂measureU = 0 := by
  rw [integral_eval_U_real_mul_eval_U_real_measureU, classicalMeasureT_eq,
    integral_eval_T_real_measureT_of_ne_zero (by omega),
    integral_eval_T_real_measureT_of_ne_zero (by omega)]
  simp

/-- Squared norms of second-kind Chebyshev polynomials (DLMF Table 18.3.1). -/
theorem integral_eval_U_real_mul_self_measureU (n : ℕ) :
    ∫ x, (U ℝ n).eval x * (U ℝ n).eval x ∂measureU = π / 2 := by
  rw [integral_eval_U_real_mul_eval_U_real_measureU, classicalMeasureT_eq, sub_self,
    integral_eval_T_real_measureT_zero,
    integral_eval_T_real_measureT_of_ne_zero (by omega), sub_zero]

end Polynomial.Chebyshev
