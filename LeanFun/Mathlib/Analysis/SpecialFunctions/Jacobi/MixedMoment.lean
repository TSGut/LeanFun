/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Rodrigues
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Mass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.LinearCombination

/-!
# Mixed Jacobi moments

Integration by parts computes connection coefficients without restrictions on
source parameters. Only the integrating weight needs integrable endpoints.
Reference: DLMF 18.18.14.
-/

public section
open MeasureTheory Set Real
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- Multiplication by `1+x` raises the second weight parameter (DLMF 18.3). -/
private theorem jacobiWeight_beta_add_one (α β : ℝ) (x : Ioo (-1 : ℝ) 1) :
    (jacobiWeight α (β + 1) x : ℝ) = (1 + (x : ℝ)) * (jacobiWeight α β x : ℝ) := by
  simp only [jacobiWeight_apply]
  rw [rpow_add (by linarith [x.property.1] : 0 < 1 + (x : ℝ)), rpow_one]
  ring

/-- A Rodrigues derivative with different source and weight parameters
(DLMF 18.18.14). -/
private theorem hasDerivAt_jacobiWeight_mul_jacobi_mixed_onOpen (α β γ : ℝ) (n : ℕ)
    (x : Ioo (-1 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (jacobiWeight (α + 1) (β + 1) y : ℝ) *
        (jacobi (γ + 1) (β + 1) n).eval (y : ℝ))
      ((γ - α) * ((jacobiWeight α (β + 1) x : ℝ) * (jacobi (γ + 1) (β + 1) n).eval (x : ℝ)) -
        2 * (n + 1 : ℝ) * ((jacobiWeight α β x : ℝ) * (jacobi γ β (n + 1)).eval (x : ℝ))) x := by
  have hd := (hasDerivAt_jacobiWeight_add_one α β x).mul
    ⟨_, fun _ ↦ rfl, (jacobi (γ + 1) (β + 1) n).hasDerivAt (x : ℝ)⟩
  have he := congrArg (fun p : ℝ[X] ↦ p.eval (x : ℝ)) (jacobi_rodrigues_step γ β n)
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_one, eval_X, eval_C, eval_neg] at he
  convert hd using 1
  rw [jacobiWeight_add_one, jacobiWeight_beta_add_one]
  linear_combination -(jacobiWeight α β x : ℝ) * he

/-- A Rodrigues derivative with different source and weight parameters
(DLMF 18.18.14). -/
theorem hasDerivAt_jacobiWeight_mul_jacobi_mixed (α β γ : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    HasDerivAt (fun t ↦ ((1 - (t : ℝ)) ^ ((α + 1)) * (1 + (t : ℝ)) ^ ((β + 1))) *
      (jacobi (γ + 1) (β + 1) n).eval t)
      ((γ - α) * (((1 - (x : ℝ)) ^ (α) * (1 + (x : ℝ)) ^ ((β + 1))) * (jacobi (γ + 1) (β + 1) n).eval x) -
        2 * (n + 1 : ℝ) * (((1 - (x : ℝ)) ^ (α) * (1 + (x : ℝ)) ^ (β)) * (jacobi γ β (n + 1)).eval x)) x := by
  exact (hasDerivAtOnOpen_iff _ _ _ ⟨x, hx⟩ _ (fun _ ↦ rfl)).mp
    (hasDerivAt_jacobiWeight_mul_jacobi_mixed_onOpen α β γ n ⟨x, hx⟩)

/-- A one-step mixed-moment recurrence, with unrestricted source parameter `γ`
(DLMF 18.18.14). -/
theorem integral_jacobi_mixed_succ {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (γ : ℝ) (n : ℕ) :
    2 * (n + 1 : ℝ) * (∫ x, (jacobi γ β (n + 1)).eval x ∂jacobiMeasure α β) =
      (γ - α) * ∫ x, (jacobi (γ + 1) (β + 1) n).eval x ∂jacobiMeasure α (β + 1) := by
  have hi0 := integrable_jacobiMeasure hα hβ (jacobi γ β (n + 1)).continuous.continuousOn
  have hi1 := integrable_jacobiMeasure hα (by linarith : -1 < β + 1)
    (jacobi (γ + 1) (β + 1) n).continuous.continuousOn
  have hw0 := (integrable_jacobiMeasure_iff _ _ _).mp hi0
  have hw1 := (integrable_jacobiMeasure_iff _ _ _).mp hi1
  have hi := integral_eq_zero_of_hasDerivAt_jacobiWeight_mul hα hβ
    (jacobi (γ + 1) (β + 1) n).continuous.continuousOn
    (hasDerivAt_jacobiWeight_mul_jacobi_mixed_onOpen α β γ n)
    ((hw1.const_mul (γ - α)).sub (hw0.const_mul (2 * (n + 1 : ℝ))))
  rw [integral_sub (hw1.const_mul _) (hw0.const_mul _), integral_const_mul,
    integral_const_mul] at hi
  rw [integral_jacobiMeasure α β ⟨fun x ↦ (jacobi γ β (n + 1)).eval (x : ℝ), hi0⟩,
    integral_jacobiMeasure α (β + 1) ⟨fun x ↦ (jacobi (γ + 1) (β + 1) n).eval (x : ℝ), hi1⟩]
  exact (sub_eq_zero.mp hi).symm

/-- Integrating a Jacobi polynomial against a weight with a different first
parameter gives a rising factorial times a shifted mass (DLMF 18.18.14). -/
theorem integral_jacobi_mixed {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (γ : ℝ) (n : ℕ) :
    (2 : ℝ) ^ n * n.factorial * (∫ x, (jacobi γ β n).eval x ∂jacobiMeasure α β) =
      (ascPochhammer ℝ n).eval (γ - α) * ∫ _ : ℝ, (1 : ℝ) ∂jacobiMeasure α (β + n) := by
  induction n generalizing β γ with
  | zero => simp
  | succ n ih =>
    have hm := integral_jacobi_mixed_succ hα hβ γ n
    have hi := ih (by linarith : -1 < β + 1) (γ + 1)
    rw [ascPochhammer_succ_left]
    simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
    rw [show γ + 1 - α = γ - α + 1 by ring,
      show β + 1 + (n : ℝ) = β + (n + 1 : ℕ) by push_cast; ring] at hi
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    push_cast at hi
    linear_combination (2 : ℝ) ^ n * n.factorial * hm + (γ - α) * hi

end Polynomial
