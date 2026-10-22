/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Mass
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.PolynomialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Parameter shifts of Jacobi mass

The Beta integral and Gamma recurrence express integer shifts using rising
factorials. References: DLMF 5.5.1 and 18.18.14.
-/

public section
open MeasureTheory Real
namespace Polynomial

/-- Raising the second weight parameter shifts the mass by a Pochhammer ratio,
with the denominator cleared (DLMF 18.18.14). -/
theorem integral_one_jacobiMeasure_beta_add_nat {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (m : ℕ) :
    (ascPochhammer ℝ m).eval (α + β + 2) *
        (∫ _ : ℝ, (1 : ℝ) ∂jacobiMeasure α (β + m)) =
      (2 : ℝ) ^ m * (ascPochhammer ℝ m).eval (β + 1) *
        ∫ _ : ℝ, (1 : ℝ) ∂jacobiMeasure α β := by
  have hβm : -1 < β + (m : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hβΓ := Gamma_add_nat_eq_ascPochhammer_mul (by linarith : 0 < β + 1) m
  have hαβΓ := Gamma_add_nat_eq_ascPochhammer_mul (by linarith : 0 < α + β + 2) m
  simp only [GammaOn, GammaPoint.ofPos] at hβΓ hαβΓ
  rw [integral_one_jacobiMeasure hα hβm, integral_one_jacobiMeasure hα hβ]
  simp only [GammaOn, GammaPoint.ofPos]
  rw [show α + (β + (m : ℝ)) + 1 = (α + β + 1) + m by ring,
    rpow_add (by norm_num : (0 : ℝ) < 2), rpow_natCast,
    show β + (m : ℝ) + 1 = (β + 1) + m by ring,
    hβΓ,
    show α + (β + (m : ℝ)) + 2 = (α + β + 2) + m by ring,
    hαβΓ]
  have hp : (ascPochhammer ℝ m).eval (α + β + 2) ≠ 0 :=
    (ascPochhammer_pos m (α + β + 2) (by linarith)).ne'
  field_simp

end Polynomial
