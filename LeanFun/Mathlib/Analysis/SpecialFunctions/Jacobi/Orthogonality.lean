/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Weight
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialEquation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Uniqueness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.LinearCombination

/-! # Jacobi orthogonality
The weighted Wronskian proves orthogonality throughout α, β > -1.
Reference: DLMF Table 18.3.1.
-/
public section
open MeasureTheory Set Real
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- The top coefficient is positive in the orthogonality range (DLMF Table 18.3.1). -/
theorem coeff_jacobi_self_pos {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    0 < (jacobi α β n).coeff n := by
  rcases n with _ | n
  · simp
  rw [coeff_jacobi_self]
  apply mul_pos
  · positivity
  · apply ascPochhammer_pos
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Exact degree in the orthogonality range (DLMF Table 18.3.1). -/
theorem degree_jacobi_of_neg_one_lt {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (jacobi α β n).degree = n :=
  degree_eq_of_le_of_coeff_ne_zero (degree_jacobi_le α β n) (coeff_jacobi_self_pos hα hβ n).ne'

/-- Jacobi polynomials as a degree-indexed sequence (DLMF Table 18.3.1). -/
@[expose] noncomputable def jacobiSequence {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) : Sequence ℝ where
  elems' := jacobi α β
  degree_eq' := degree_jacobi_of_neg_one_lt hα hβ

/-- The sequence uses the existing Jacobi polynomials (DLMF Table 18.3.1). -/
@[simp] theorem jacobiSequence_apply {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    jacobiSequence hα hβ n = jacobi α β n := rfl

private theorem jacobi_wronskian_hasDerivAt (α β : ℝ) (m n : ℕ)
    (x : Ioo (-1 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (jacobiWeight (α + 1) (β + 1) y : ℝ) *
        ((jacobi α β m).derivative.eval (y : ℝ) * (jacobi α β n).eval (y : ℝ) -
         (jacobi α β m).eval (y : ℝ) * (jacobi α β n).derivative.eval (y : ℝ)))
      ((jacobiWeight α β x : ℝ) * (((n : ℝ) * (n + α + β + 1) -
        (m : ℝ) * (m + α + β + 1)) * (jacobi α β m).eval (x : ℝ) * (jacobi α β n).eval (x : ℝ))) x := by
  have hq := (((jacobi α β m).derivative.hasDerivAt (x : ℝ)).mul
    ((jacobi α β n).hasDerivAt (x : ℝ))).sub
      (((jacobi α β m).hasDerivAt (x : ℝ)).mul ((jacobi α β n).derivative.hasDerivAt (x : ℝ)))
  have hd := (hasDerivAt_jacobiWeight_add_one α β x).mul
    ⟨_, fun _ ↦ rfl, hq⟩
  convert hd using 1
  simp only [Pi.mul_apply, Pi.sub_apply]
  rw [jacobiWeight_add_one]
  have hm := congrArg (fun p : ℝ[X] ↦ p.eval (x : ℝ)) (jacobi_differentialEquation α β m)
  have hn := congrArg (fun p : ℝ[X] ↦ p.eval (x : ℝ)) (jacobi_differentialEquation α β n)
  simp only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C, eval_zero] at hm hn
  linear_combination -((jacobiWeight α β x : ℝ) * (jacobi α β n).eval (x : ℝ)) * hm +
    ((jacobiWeight α β x : ℝ) * (jacobi α β m).eval (x : ℝ)) * hn

/-- Distinct Jacobi polynomials are orthogonal (DLMF Table 18.3.1). -/
theorem integral_mul_jacobi_eq_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {m n : ℕ} (hmn : m ≠ n) :
    ∫ x, (jacobi α β m).eval x * (jacobi α β n).eval x ∂jacobiMeasure α β = 0 := by
  let c : ℝ := (n : ℝ) * (n + α + β + 1) - (m : ℝ) * (m + α + β + 1)
  have hint := integrable_jacobiMeasure hα hβ
    ((jacobi α β m).continuous.mul (jacobi α β n).continuous).continuousOn
  have hw := (integrable_jacobiMeasure_iff _ _ _).mp hint
  have hi := integral_eq_zero_of_hasDerivAt_jacobiWeight_mul hα hβ
    (((jacobi α β m).derivative.continuous.mul (jacobi α β n).continuous).sub
      ((jacobi α β m).continuous.mul (jacobi α β n).derivative.continuous)).continuousOn
    (jacobi_wronskian_hasDerivAt α β m n)
    (by convert hw.const_mul c using 1; ext x; dsimp [c]; ring)
  have hc : c ≠ 0 := by
    have hnm : (n : ℝ) ≠ m := by exact_mod_cast hmn.symm
    have hs : 1 ≤ n + m := by omega
    have hs' : (1 : ℝ) ≤ (n : ℝ) + m := by exact_mod_cast hs
    have hf : c = ((n : ℝ) - m) * ((n : ℝ) + m + α + β + 1) := by dsimp [c]; ring
    rw [hf]
    exact mul_ne_zero (sub_ne_zero.mpr hnm) (ne_of_gt (by linarith))
  rw [integral_jacobiMeasure α β
    ⟨fun x ↦ (jacobi α β m).eval (x : ℝ) * (jacobi α β n).eval (x : ℝ), hint⟩]
  apply (mul_eq_zero.mp (show c * (∫ x : Ioo (-1 : ℝ) 1,
      (jacobiWeight α β x : ℝ) * ((jacobi α β m).eval (x : ℝ) * (jacobi α β n).eval (x : ℝ))) = 0 from ?_)).resolve_left hc
  rw [← integral_const_mul]
  convert hi using 1
  congr 1
  funext x
  dsimp [c]
  ring

/-- The Jacobi sequence satisfies the general orthogonality predicate (DLMF Table 18.3.1). -/
theorem isOrthogonal_jacobiSequence {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    (jacobiSequence hα hβ).IsOrthogonal (jacobiMeasure α β) where
  integrable _ _ := (hasFiniteMoments_jacobiMeasure hα hβ).integrable_mul _ _
  orthogonal _ _ hmn := integral_mul_jacobi_eq_zero hα hβ hmn

end Polynomial
