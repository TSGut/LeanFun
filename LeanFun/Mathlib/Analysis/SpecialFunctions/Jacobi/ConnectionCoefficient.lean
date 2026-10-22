/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.MixedInner
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.MassShift
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Completeness
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.FiniteConnection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Recurrence
import Mathlib.Tactic.FieldSimp

/-!
# Explicit one-parameter Jacobi connection coefficients

The coefficient from degree `k+m` to degree `k` is a quotient of rising
factorials. The target satisfies alpha,beta > -1, but the source first parameter
is unrestricted. The formula removes the removable singularity at alpha+beta+1=0.
Reference: DLMF 18.18.14.
-/

public section
open MeasureTheory Real
namespace Polynomial

/-- The target leading rising factorial is positive, including degree zero
when its base need not be positive (DLMF Table 18.3.1). -/
theorem ascPochhammer_jacobi_leading_pos {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (k : ℕ) :
    0 < (ascPochhammer ℝ k).eval ((k : ℝ) + α + β + 1) := by
  cases k with
  | zero => simp
  | succ k =>
    apply ascPochhammer_pos
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]

/-- Jacobi basis coordinates are the integral coefficients of a polynomial
(DLMF 18.18.1). -/
theorem jacobiBasis_repr_eq_coefficient {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (p : ℝ[X]) (k : ℕ) :
    (jacobiBasis hα hβ).repr p k = jacobiCoefficient α β (IntegralCoefficientInput.ofPolynomial
      (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)
      (jacobi α β k) (by simpa only [jacobiSequence_apply] using (jacobiSequence hα hβ).ne_zero k) p) := by
  rw [jacobiBasis, (isOrthogonal_jacobiSequence hα hβ).basis_repr_eq_integralInner_div
    (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)]
  simp only [jacobiSequence_apply, integralInner, jacobiCoefficient, IntegralCoefficientInput.ofPolynomial_val, pow_two, div_eq_mul_inv]
  ring

/-- The one-parameter Jacobi connection coefficient, without a spurious
exception at alpha+beta+1=0 (DLMF 18.18.14). -/
theorem jacobiCoefficient_jacobi_add {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (γ : ℝ) (k m : ℕ) :
    jacobiCoefficient α β (IntegralCoefficientInput.ofPolynomial
      (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)
      (jacobi α β k) (by simpa only [jacobiSequence_apply] using (jacobiSequence hα hβ).ne_zero k) (jacobi γ β (k + m))) =
      ((ascPochhammer ℝ m).eval (β + k + 1) *
        (ascPochhammer ℝ k).eval ((k + m : ℕ) + γ + β + 1) *
        (ascPochhammer ℝ m).eval (γ - α)) /
      ((ascPochhammer ℝ k).eval ((k : ℝ) + α + β + 1) *
        (ascPochhammer ℝ m).eval (α + β + 2 * k + 2) * m.factorial) := by
  have hak : -1 < α + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hbk : -1 < β + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hd := integral_jacobi_mul_jacobi_shift hα hβ γ k m
  have hm := integral_jacobi_mixed hak hbk (γ + k) m
  have hs := integral_one_jacobiMeasure_beta_add_nat hak hbk m
  have hn := integral_jacobi_mul_jacobi_shift hα hβ α k 0
  simp only [Nat.add_zero, jacobi_zero, eval_one, ← pow_two] at hn
  rw [show γ + (k : ℝ) - (α + k) = γ - α by ring] at hm
  rw [show α + (k : ℝ) + (β + k) + 2 = α + β + 2 * k + 2 by ring] at hs
  have ha : (4 : ℝ) ^ k * k.factorial ≠ 0 := by positivity
  have hb : (2 : ℝ) ^ m * m.factorial ≠ 0 := by positivity
  have hS : (ascPochhammer ℝ m).eval (α + β + 2 * k + 2) ≠ 0 :=
    (ascPochhammer_pos m _ (by linarith [Nat.cast_nonneg (α := ℝ) k])).ne'
  have hH := (ascPochhammer_jacobi_leading_pos hα hβ k).ne'
  have hmass : (∫ _ : ℝ, (1 : ℝ) ∂jacobiMeasure (α + k) (β + k)) ≠ 0 := by
    rw [integral_one_jacobiMeasure hak hbk]
    simp only [GammaOn, GammaPoint.ofPos]
    have ha' := Gamma_pos_of_pos (show 0 < α + (k : ℝ) + 1 by linarith)
    have hb' := Gamma_pos_of_pos (show 0 < β + (k : ℝ) + 1 by linarith)
    have hs' := Gamma_pos_of_pos (show 0 < α + (k : ℝ) + (β + k) + 2 by linarith)
    positivity
  rw [mul_comm ((4 : ℝ) ^ k * k.factorial)] at hd hn
  rw [mul_comm ((2 : ℝ) ^ m * m.factorial)] at hm
  rw [mul_comm ((ascPochhammer ℝ m).eval (α + β + 2 * k + 2))] at hs
  have hj := (eq_div_iff ha).mpr hd
  have hi := (eq_div_iff hb).mpr hm
  have hl := (eq_div_iff hS).mpr hs
  have hh := (eq_div_iff ha).mpr hn
  rw [jacobiCoefficient, IntegralCoefficientInput.ofPolynomial_val, hj, hi, hl, hh]
  field_simp

end Polynomial
