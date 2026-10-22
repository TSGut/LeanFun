/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Measure

/-! # Changes of density for Gegenbauer measures

Multiplication by a power of `1-x²` shifts the weight parameter (DLMF Table 18.3.1).
No finiteness assumption is required for equality of these measures.
-/

public section
open MeasureTheory Set Real
namespace Polynomial

/-- Multiplication of classical open-domain weights shifts the parameter.
Here the second weight has exponent p. Reference: DLMF Table 18.3.1. -/
theorem gegenbauerMeasure_shift (lam p : ℝ) :
    openIntervalWeightMeasure (-1) 1
      (gegenbauerWeight lam * gegenbauerWeight (p + 1 / 2)) =
      gegenbauerMeasure (lam+p) := by
  change openIntervalWeightMeasure (-1) 1 _ = openIntervalWeightMeasure (-1) 1 _
  congr 1
  ext x
  simp only [ContinuousMap.mul_apply, NNReal.coe_mul, gegenbauerWeight_apply]
  have hp : 0 < 1 - (x : ℝ)^2 := by nlinarith [x.property.1,x.property.2]
  rw [← Real.rpow_add hp]
  congr 1
  ring


end Polynomial
