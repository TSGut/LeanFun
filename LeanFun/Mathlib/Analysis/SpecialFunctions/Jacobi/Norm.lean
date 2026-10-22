/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Mass
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Jacobi squared norms
Integration by parts shifts both parameters and lowers the degree.
The zero-degree formula is stated separately (DLMF Table 18.3.1).
-/
public section
open MeasureTheory Set Real
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

private theorem jacobi_energy_hasDerivAt (α β : ℝ) (n : ℕ)
    (x : Ioo (-1 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (jacobiWeight (α + 1) (β + 1) y : ℝ) *
        ((jacobi α β n).derivative.eval (y : ℝ) * (jacobi α β n).eval (y : ℝ)))
      ((jacobiWeight (α + 1) (β + 1) x : ℝ) * (jacobi α β n).derivative.eval (x : ℝ) ^ 2 -
        ((n : ℝ) * (n + α + β + 1)) *
          ((jacobiWeight α β x : ℝ) * (jacobi α β n).eval (x : ℝ) ^ 2)) x := by
  have hq := ((jacobi α β n).derivative.hasDerivAt (x : ℝ)).mul
    ((jacobi α β n).hasDerivAt (x : ℝ))
  have hd := (hasDerivAt_jacobiWeight_add_one α β x).mul ⟨_, fun _ ↦ rfl, hq⟩
  convert hd using 1
  simp only [Pi.mul_apply]
  rw [jacobiWeight_add_one]
  have he := congrArg (fun p : ℝ[X] ↦ p.eval (x : ℝ)) (jacobi_differentialEquation α β n)
  simp only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C, eval_zero] at he
  linear_combination -((jacobiWeight α β x : ℝ) * (jacobi α β n).eval (x : ℝ)) * he

/-- The Jacobi energy identity (DLMF Tables 18.3.1 and 18.8.1). -/
theorem integral_sq_derivative_jacobi {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∫ x, (jacobi α β n).derivative.eval x ^ 2 ∂jacobiMeasure (α + 1) (β + 1) =
      ((n : ℝ) * (n + α + β + 1)) *
        ∫ x, (jacobi α β n).eval x ^ 2 ∂jacobiMeasure α β := by
  have hi0 := integrable_jacobiMeasure hα hβ
    ((jacobi α β n).continuous.pow 2).continuousOn
  have hi1 := integrable_jacobiMeasure (by linarith : -1 < α + 1)
    (by linarith : -1 < β + 1) ((jacobi α β n).derivative.continuous.pow 2).continuousOn
  have hw0 := (integrable_jacobiMeasure_iff _ _ _).mp hi0
  have hw1 := (integrable_jacobiMeasure_iff _ _ _).mp hi1
  simp only [Pi.pow_apply] at hw0 hw1
  have hi := integral_eq_zero_of_hasDerivAt_jacobiWeight_mul hα hβ
    ((jacobi α β n).derivative.continuous.mul (jacobi α β n).continuous).continuousOn
    (jacobi_energy_hasDerivAt α β n)
    (hw1.sub (hw0.const_mul ((n : ℝ) * (n + α + β + 1))))
  rw [integral_sub hw1 (hw0.const_mul _), integral_const_mul] at hi
  rw [integral_jacobiMeasure (α + 1) (β + 1)
    ⟨fun x ↦ (jacobi α β n).derivative.eval (x : ℝ) ^ 2, hi1⟩,
    integral_jacobiMeasure α β ⟨fun x ↦ (jacobi α β n).eval (x : ℝ) ^ 2, hi0⟩]
  exact sub_eq_zero.mp hi

/-- Lower the degree and raise both parameters in the squared norm
(DLMF 18.9.15 and Table 18.3.1). -/
theorem integral_sq_jacobi_succ_shift {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (∫ x, (jacobi α β (n + 1)).eval x ^ 2 ∂jacobiMeasure α β) =
      ((n : ℝ) + α + β + 2) / (4 * (n + 1)) *
        ∫ x, (jacobi (α + 1) (β + 1) n).eval x ^ 2 ∂jacobiMeasure (α + 1) (β + 1) := by
  have he := integral_sq_derivative_jacobi hα hβ (n + 1)
  have hd (x : ℝ) : (jacobi α β (n + 1)).derivative.eval (x : ℝ) =
      (((n : ℝ) + α + β + 2) / 2) * (jacobi (α + 1) (β + 1) n).eval (x : ℝ) := by
    rw [derivative_jacobi_succ, eval_mul, eval_C]
    norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  simp_rw [hd, mul_pow] at he
  rw [integral_const_mul] at he
  have hc : 0 < (n : ℝ) + α + β + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn : 0 < (n + 1 : ℝ) := by positivity
  apply mul_left_cancel₀ (mul_ne_zero hn.ne' hc.ne')
  calc
    _ = ((((n : ℝ) + α + β + 2) / 2) ^ 2) *
        ∫ x, (jacobi (α + 1) (β + 1) n).eval (x : ℝ) ^ 2 ∂jacobiMeasure (α + 1) (β + 1) := by
      convert he.symm using 1
      push_cast
      ring
    _ = _ := by field_simp; ring

/-- The degree-zero squared norm, with no singular Gamma quotient
(DLMF Table 18.3.1). -/
private theorem integral_sq_jacobi_zero_gamma_formula {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ∫ x, (jacobi α β 0).eval x ^ 2 ∂jacobiMeasure α β =
      (2 : ℝ) ^ (α + β + 1) * Gamma (α + 1) * Gamma (β + 1) / Gamma (α + β + 2) := by
  simpa [GammaOn, GammaPoint.ofPos] using integral_one_jacobiMeasure hα hβ

/-- The positive-degree Jacobi squared norms in the standard Gamma form
(DLMF Table 18.3.1). -/
private theorem integral_sq_jacobi_succ_gamma_formula {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∫ x, (jacobi α β (n + 1)).eval x ^ 2 ∂jacobiMeasure α β =
      (2 : ℝ) ^ (α + β + 1) * Gamma (n + α + 2) * Gamma (n + β + 2) /
        ((2 * n + α + β + 3) * Gamma (n + α + β + 2) * (n + 1).factorial) := by
  induction n generalizing α β with
  | zero =>
    rw [integral_sq_jacobi_succ_shift hα hβ,
      integral_sq_jacobi_zero_gamma_formula (by linarith : -1 < α + 1) (by linarith : -1 < β + 1)]
    have hs2 : 0 < α + β + 2 := by linarith
    have hs3 : 0 < α + β + 3 := by linarith
    have hp : (2 : ℝ) ^ ((α + 1) + (β + 1) + 1) = 4 * (2 : ℝ) ^ (α + β + 1) := by
      rw [show (α + 1) + (β + 1) + 1 = (α + β + 1) + 2 by ring,
        Real.rpow_add (by norm_num), Real.rpow_two]
      ring
    have hg : Gamma ((α + 1) + (β + 1) + 2) =
        (α + β + 3) * (α + β + 2) * Gamma (α + β + 2) := by
      rw [show (α + 1) + (β + 1) + 2 = (α + β + 2) + 1 + 1 by ring,
        Gamma_add_one (by linarith : α + β + 2 + 1 ≠ 0), Gamma_add_one hs2.ne']
      ring
    rw [hp, hg]
    norm_num only [Nat.cast_zero, zero_add, mul_zero, Nat.factorial_one, Nat.cast_one, mul_one]
    rw [show α + 1 + 1 = α + 2 by ring, show β + 1 + 1 = β + 2 by ring]
    field_simp
  | succ n ih =>
    rw [integral_sq_jacobi_succ_shift hα hβ,
      ih (by linarith : -1 < α + 1) (by linarith : -1 < β + 1)]
    have hs : 0 < (n : ℝ) + α + β + 3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hp : (2 : ℝ) ^ ((α + 1) + (β + 1) + 1) = 4 * (2 : ℝ) ^ (α + β + 1) := by
      rw [show (α + 1) + (β + 1) + 1 = (α + β + 1) + 2 by ring,
        Real.rpow_add (by norm_num), Real.rpow_two]
      ring
    have hg : Gamma ((n : ℝ) + (α + 1) + (β + 1) + 2) =
        ((n : ℝ) + α + β + 3) * Gamma ((n : ℝ) + α + β + 3) := by
      rw [show (n : ℝ) + (α + 1) + (β + 1) + 2 = (n + α + β + 3) + 1 by ring,
        Gamma_add_one hs.ne']
    rw [hp, hg]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have ha : (n : ℝ) + (α + 1) + 2 = (n + 1) + α + 2 := by ring
    have hb : (n : ℝ) + (β + 1) + 2 = (n + 1) + β + 2 := by ring
    have hc : (n : ℝ) + 1 + α + β + 2 = n + α + β + 3 := by ring
    rw [ha, hb, hc]
    field_simp
    ring

/-- The classical Gamma formula; every displayed Gamma value excludes its poles. -/
theorem integral_sq_jacobi_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ∫ x, (jacobi α β 0).eval x ^ 2 ∂jacobiMeasure α β =
      (2 : ℝ) ^ (α + β + 1) * GammaOn (GammaPoint.ofPos (α + 1) (by linarith)) * GammaOn (GammaPoint.ofPos (β + 1) (by linarith)) / GammaOn (GammaPoint.ofPos (α + β + 2) (by linarith)) :=
  integral_sq_jacobi_zero_gamma_formula hα hβ

/-- The classical Gamma formula; every displayed Gamma value excludes its poles. -/
theorem integral_sq_jacobi_succ {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∫ x, (jacobi α β (n + 1)).eval x ^ 2 ∂jacobiMeasure α β =
      (2 : ℝ) ^ (α + β + 1) * GammaOn (GammaPoint.ofPos (n + α + 2) (by have _hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)) * GammaOn (GammaPoint.ofPos (n + β + 2) (by have _hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)) /
        ((2 * n + α + β + 3) * GammaOn (GammaPoint.ofPos (n + α + β + 2) (by have _hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)) * (n + 1).factorial) :=
  integral_sq_jacobi_succ_gamma_formula hα hβ n

end Polynomial
