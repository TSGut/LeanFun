/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.MixedMoment
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.LinearCombination

/-!
# Mixed Jacobi inner products

Integration by parts moves derivatives to the source polynomial and shifts the
target weight. Reference: DLMF 18.18.14.
-/

public section
open MeasureTheory Set Real
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

private theorem hasDerivAt_jacobiWeight_mul_polynomial_mul_jacobi
    (α β : ℝ) (q : ℝ[X]) (k : ℕ) (x : Ioo (-1 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (jacobiWeight (α + 1) (β + 1) y : ℝ) *
        (q.eval (y : ℝ) * (jacobi (α + 1) (β + 1) k).eval (y : ℝ)))
      ((jacobiWeight (α + 1) (β + 1) x : ℝ) *
        (q.derivative.eval (x : ℝ) * (jacobi (α + 1) (β + 1) k).eval (x : ℝ)) -
       2 * (k + 1 : ℝ) * ((jacobiWeight α β x : ℝ) * (q.eval (x : ℝ) * (jacobi α β (k + 1)).eval (x : ℝ)))) x := by
  have hq : HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ q.eval (y : ℝ)) (q.derivative.eval (x : ℝ)) x :=
    ⟨_, fun _ ↦ rfl, q.hasDerivAt (x : ℝ)⟩
  convert hq.mul (hasDerivAt_jacobiWeight_mul_jacobi α β k x) using 1
  · funext y
    ring
  · ring

/-- Integration by parts against a positive-degree Jacobi polynomial
(DLMF 18.18.14). -/
theorem integral_mul_jacobi_succ {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (q : ℝ[X]) (k : ℕ) :
    2 * (k + 1 : ℝ) * (∫ x, q.eval x * (jacobi α β (k + 1)).eval x ∂jacobiMeasure α β) =
      ∫ x, q.derivative.eval x * (jacobi (α + 1) (β + 1) k).eval x
        ∂jacobiMeasure (α + 1) (β + 1) := by
  have hi0 := integrable_jacobiMeasure hα hβ
    (q.continuous.mul (jacobi α β (k + 1)).continuous).continuousOn
  have hi1 := integrable_jacobiMeasure (by linarith : -1 < α + 1)
    (by linarith : -1 < β + 1)
    (q.derivative.continuous.mul (jacobi (α + 1) (β + 1) k).continuous).continuousOn
  have hw0 := (integrable_jacobiMeasure_iff _ _ _).mp hi0
  have hw1 := (integrable_jacobiMeasure_iff _ _ _).mp hi1
  simp only [Pi.mul_apply] at hw0 hw1
  have hi := integral_eq_zero_of_hasDerivAt_jacobiWeight_mul hα hβ
    (q.continuous.mul (jacobi (α + 1) (β + 1) k).continuous).continuousOn
    (hasDerivAt_jacobiWeight_mul_polynomial_mul_jacobi α β q k)
    (hw1.sub (hw0.const_mul (2 * (k + 1 : ℝ))))
  rw [integral_sub hw1 (hw0.const_mul _), integral_const_mul] at hi
  rw [integral_jacobiMeasure α β
    ⟨fun x ↦ q.eval (x : ℝ) * (jacobi α β (k + 1)).eval (x : ℝ), hi0⟩,
    integral_jacobiMeasure (α + 1) (β + 1)
      ⟨fun x ↦ q.derivative.eval (x : ℝ) * (jacobi (α + 1) (β + 1) k).eval (x : ℝ), hi1⟩]
  exact (sub_eq_zero.mp hi).symm

/-- Repeated integration by parts lowers the source and target degrees together.
The source first parameter is unrestricted (DLMF 18.18.14). -/
theorem integral_jacobi_mul_jacobi_shift {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (γ : ℝ) (k m : ℕ) :
    (4 : ℝ) ^ k * k.factorial *
      (∫ x, (jacobi γ β (k + m)).eval x * (jacobi α β k).eval x ∂jacobiMeasure α β) =
      (ascPochhammer ℝ k).eval ((k + m : ℕ) + γ + β + 1) *
        ∫ x, (jacobi (γ + k) (β + k) m).eval x ∂jacobiMeasure (α + k) (β + k) := by
  induction k generalizing α β γ with
  | zero => simp
  | succ k ih =>
    have hb := integral_mul_jacobi_succ hα hβ (jacobi γ β (k + 1 + m)) k
    have hd (x : ℝ) : (jacobi γ β (k + 1 + m)).derivative.eval (x : ℝ) =
        (((k + m : ℕ) + γ + β + 2) / 2) * (jacobi (γ + 1) (β + 1) (k + m)).eval (x : ℝ) := by
      rw [show k + 1 + m = (k + m) + 1 by omega, derivative_jacobi_succ, eval_mul, eval_C]
      norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    simp_rw [hd, mul_assoc] at hb
    rw [integral_const_mul] at hb
    have hi := ih (by linarith : -1 < α + 1) (by linarith : -1 < β + 1) (γ + 1)
    rw [ascPochhammer_succ_left]
    simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
    have ha : α + 1 + (k : ℝ) = α + (k + 1 : ℕ) := by push_cast; ring
    have hβ' : β + 1 + (k : ℝ) = β + (k + 1 : ℕ) := by push_cast; ring
    have hγ : γ + 1 + (k : ℝ) = γ + (k + 1 : ℕ) := by push_cast; ring
    rw [ha, hβ', hγ] at hi
    rw [show (k + m : ℕ) + (γ + 1) + (β + 1) + 1 =
      (k + 1 + m : ℕ) + γ + β + 1 + 1 by push_cast; ring] at hi
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    push_cast at hi hb ⊢
    linear_combination 2 * (4 : ℝ) ^ k * k.factorial * hb +
      ((k : ℝ) + m + γ + β + 2) * hi

end Polynomial
