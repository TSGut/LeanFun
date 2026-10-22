/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.TotalDegree
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalSequence

import Mathlib.Topology.Algebra.Polynomial

/-! # Sparse coordinate multiplication in the Proriol basis
The x coordinate preserves inner degree; y changes it by at most one.
Together with total-degree orthogonality this gives banded blocks in a block
tridiagonal matrix. Reference: DLMF 18.37 and Dunkl–Xu, §2.6.1.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- Pairings with monomial multipliers separate in the Duffy coordinates. -/
theorem integralInner_monomial_mul_proriol {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n k m j a b : ℕ) :
    integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) (X 0^a * X 1^b * proriol α β γ n k) (proriol α β γ m j)) =
      (∫ x, (shiftedJacobi α (β+γ+2*k+1) (n-k)).eval x *
        (shiftedJacobi α (β+γ+2*j+1) (m-j)).eval x * x^(k+j+a+b)
        ∂unitJacobiMeasure α (β+γ+1)) *
      Polynomial.integralInner (unitJacobiMeasure β γ) (Polynomial.IntegrablePair.of (unitJacobiMeasure β γ) (Polynomial.X^b * shiftedJacobi β γ k) (shiftedJacobi β γ j)) := by
  let := isFiniteMeasure_unitJacobiMeasure hα (show -1 < β+γ+1 by linarith)
  let := isFiniteMeasure_unitJacobiMeasure hβ hγ
  have he := (koornwinderMeasure_integral_univ (fun x => x) continuous_id
    (unitJacobiMeasure α (β+γ+1)) (unitJacobiMeasure β γ)
    ⟨fun v ↦ eval v ((X 0^a * X 1^b * proriol α β γ n k) * proriol α β γ m j), by
      simpa only [proriolProductMeasure, map_one, mul_one] using
        (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul ((X 0^a * X 1^b * proriol α β γ n k) * proriol α β γ m j) 1⟩).2
  simp only [map_mul, map_pow, eval_X] at he
  simp only [integralInner, proriolProductMeasure]
  simp only [map_mul, map_pow, eval_X]
  rw [he, Polynomial.integralInner, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  change v.1^a * (v.1*v.2)^b * eval (![v.1,v.1*v.2] : Fin 2 → ℝ) _ *
    eval (![v.1,v.1*v.2] : Fin 2 → ℝ) _ = _
  rw [eval_proriol_scaled, eval_proriol_scaled]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, pow_add, mul_pow]
  ring

/-- Multiplication by x preserves the inner Jacobi index. -/
theorem integralInner_X_zero_mul_proriol_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n k m j : ℕ) (hkj : k ≠ j) :
    integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) (X 0 * proriol α β γ n k) (proriol α β γ m j)) = 0 := by
  have he := integralInner_monomial_mul_proriol hα hβ hγ n k m j 1 0
  simp only [pow_one, pow_zero, mul_one, one_mul] at he
  rw [he, integralInner_shiftedJacobi β γ k j
    (hi := (hasFiniteMoments_jacobiMeasure hβ hγ).integrable_mul _ _), Polynomial.integralInner,
    integral_mul_jacobi_eq_zero hβ hγ hkj, mul_zero]

/-- Multiplication by y changes the inner Jacobi index by at most one. -/
theorem integralInner_X_one_mul_proriol_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n k m j : ℕ)
    (hgap : k+1 < j ∨ j+1 < k) :
    integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) (X 1 * proriol α β γ n k) (proriol α β γ m j)) = 0 := by
  have he := integralInner_monomial_mul_proriol hα hβ hγ n k m j 0 1
  simp only [pow_one, pow_zero, one_mul] at he
  have hz := (isOrthogonal_shiftedJacobiSequence hβ hγ).integralInner_X_mul_eq_zero
    (hasFiniteMoments_unitJacobiMeasure hβ hγ) hgap
  simp only [shiftedJacobiSequence_apply] at hz
  rw [he, hz, mul_zero]

end MvPolynomial
