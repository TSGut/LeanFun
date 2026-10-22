/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Legendre.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

import all Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import all LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-! # Classical Jacobi measures
Legendre and Chebyshev use exactly the corresponding Jacobi measures. Endpoints
have zero mass, including for the integrable singular Chebyshev weight.
Reference: DLMF Table 18.3.1 and 18.7.3--4.
-/

public section
open MeasureTheory Set Real
namespace Polynomial
/-- The second-kind Chebyshev measure is the symmetric Jacobi half-parameter measure. -/
theorem measureU_eq_jacobiMeasure :
    Chebyshev.measureU = jacobiMeasure (1 / 2) (1 / 2) := by
  change openIntervalWeightMeasure (-1) 1 Chebyshev.weightU =
    openIntervalWeightMeasure (-1) 1 (jacobiWeight (1 / 2) (1 / 2))
  congr 1
  ext x
  rw [(Chebyshev.weightUT_apply x).1, jacobiWeight_apply]
  rw [← mul_rpow (by linarith [x.property.2] : 0 ≤ 1 - (x : ℝ))
    (by linarith [x.property.1] : 0 ≤ 1 + (x : ℝ)), ← sqrt_eq_rpow]
  congr 1
  ring
/-- The first-kind Chebyshev measure is the symmetric Jacobi negative-half measure. -/
theorem measureT_eq_jacobiMeasure :
    Chebyshev.classicalMeasureT = jacobiMeasure (-1 / 2) (-1 / 2) := by
  change openIntervalWeightMeasure (-1) 1 Chebyshev.weightT =
    openIntervalWeightMeasure (-1) 1 (jacobiWeight (-1 / 2) (-1 / 2))
  congr 1
  ext x
  rw [(Chebyshev.weightUT_apply x).2, jacobiWeight_apply]
  rw [← mul_rpow (by linarith [x.property.2] : 0 ≤ 1 - (x : ℝ))
    (by linarith [x.property.1] : 0 ≤ 1 + (x : ℝ))]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
    rpow_neg (mul_nonneg (by linarith [x.property.2]) (by linarith [x.property.1])),
    ← sqrt_eq_rpow]
  congr 2
  ring

/-- Legendre normalization transported to the Jacobi measure (DLMF Table 18.3.1). -/
theorem integral_sq_jacobi_zero_zero (n : ℕ) :
    ∫ x, (jacobi (0 : ℝ) 0 n).eval x ^ 2 ∂jacobiMeasure 0 0 =
      2 / (2 * (n : ℝ) + 1) := by
  rw [← legendreMeasure_eq_jacobiMeasure, ← legendre_eq_jacobi]
  exact integral_sq_legendre_measure n

/-- The second-kind Chebyshev normalization in Jacobi-measure form. -/
theorem integral_sq_chebyshev_U_jacobiMeasure (n : ℕ) :
    ∫ x, (Chebyshev.U ℝ n).eval x ^ 2 ∂jacobiMeasure (1 / 2) (1 / 2) = π / 2 := by
  rw [← measureU_eq_jacobiMeasure]
  simpa only [pow_two] using Chebyshev.integral_eval_U_real_mul_self_measureU n

/-- The first-kind Chebyshev normalization, including its exceptional constant term. -/
theorem integral_sq_chebyshev_T_jacobiMeasure (n : ℕ) :
    ∫ x, (Chebyshev.T ℝ n).eval x ^ 2 ∂jacobiMeasure (-1 / 2) (-1 / 2) =
      if n = 0 then π else π / 2 := by
  rw [← measureT_eq_jacobiMeasure, Chebyshev.classicalMeasureT_eq]
  by_cases hn : n = 0
  · subst n
    simpa only [pow_two, Nat.cast_zero, ite_true] using
      Chebyshev.integral_eval_T_real_mul_self_measureT_zero
  · simpa only [pow_two, ite_eq_right hn] using
      Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hn

end Polynomial
