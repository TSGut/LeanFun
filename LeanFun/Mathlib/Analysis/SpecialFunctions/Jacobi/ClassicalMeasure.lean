/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.MeasureTheory.Integral.ClassicalWeight
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Weight

/-! # Jacobi measures with classical domains
Reference: DLMF Table 18.3.1. The open interval contains every evaluation of
the real powers, including when the endpoint exponents are negative.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- Integer parameter shifts on the classical weight domain. -/
theorem jacobiWeight_add_nat (α β : ℝ) (k : ℕ) (x : Ioo (-1 : ℝ) 1) :
    (jacobiWeight (α + k) (β + k) x : ℝ) =
      (1 - (x : ℝ) ^ 2) ^ k * (jacobiWeight α β x : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha : α + ((k + 1 : ℕ) : ℝ) = (α + k) + 1 := by push_cast; ring
    have hb : β + ((k + 1 : ℕ) : ℝ) = (β + k) + 1 := by push_cast; ring
    rw [ha, hb, jacobiWeight_add_one, ih, pow_succ]
    ring

/-- Integer shifts preserve every classically convergent weighted integral. -/
theorem integral_jacobiMeasure_add_nat_integrable (α β : ℝ) (k : ℕ)
    (f : IntegrableInput (jacobiMeasure (α + k) (β + k))) :
    Integrable (fun x ↦ (1 - x ^ 2) ^ k * f.val x) (jacobiMeasure α β) ∧
      (∫ x, f.val x ∂jacobiMeasure (α + k) (β + k)) =
        ∫ x, (1 - x ^ 2) ^ k * f.val x ∂jacobiMeasure α β := by
  have hi : Integrable (fun x ↦ (1 - x ^ 2) ^ k * f.val x) (jacobiMeasure α β) := by
    rw [integrable_jacobiMeasure_iff]
    have h := (integrable_jacobiMeasure_iff _ _ _).1 f.property
    convert h using 1
    ext x
    rw [jacobiWeight_add_nat]
    ring
  refine ⟨hi, ?_⟩
  -- Both sides are classical weighted integrals over the open interval.
  rw [integral_jacobiMeasure (α + k) (β + k) f,
    integral_jacobiMeasure α β ⟨fun x ↦ (1 - x ^ 2) ^ k * f.val x, hi⟩]
  congr 1
  ext x
  rw [jacobiWeight_add_nat]
  ring

end Polynomial
