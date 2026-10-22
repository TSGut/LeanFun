/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ExtensionSupport

/-! # Edge pairings for Jacobi-to-Proriol extension

The shifted `(1,0)` Jacobi mode reproduces endpoint evaluation on polynomials
of no larger degree. Reference: Gutleb–Olver, arXiv:1906.03907, Section 3.1.
-/

public section
open MeasureTheory Set
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- Every shifted Jacobi polynomial with first parameter zero equals one at one. -/
theorem eval_shiftedJacobi_zero_left_one (β : ℝ) (n : ℕ) :
    (shiftedJacobi 0 β n).eval 1 = 1 := by
  rw [eval_shiftedJacobi]
  norm_num only [mul_one, sub_self, show (2 : ℝ)-1 = 1 by norm_num]
  rw [eval_jacobi_one]
  simp only [zero_add, ascPochhammer_eval_one]
  norm_num
  exact inv_mul_cancel₀ (by positivity : (n.factorial : ℝ) ≠ 0)

/-- Endpoint reproduction by a shifted `(1,0)` Jacobi mode. -/
theorem integral_shiftedJacobi_one_zero_mul (n : ℕ) (q : ℝ[X]) (hq : q.natDegree ≤ n) :
    (∫ y in (0 : ℝ)..1, (shiftedJacobi 1 0 n).eval y*q.eval y) =
      q.eval 1/((n : ℝ)+1) := by
  have hi : (∫ y in (0 : ℝ)..1, (shiftedJacobi 1 0 n).eval y) = 1/((n : ℝ)+1) := by
    rw [integral_shiftedJacobi_one_zero, eval_shiftedJacobi_zero_left_one, one_mul]
  by_cases hn : n = 0
  · subst n
    have hq0 : q.natDegree = 0 := Nat.eq_zero_of_le_zero hq
    rw [eq_C_of_natDegree_eq_zero hq0]
    simp only [eval_C, intervalIntegral.integral_mul_const, hi]
    ring
  let r := q /ₘ (X-C (1 : ℝ))
  have hr : r.natDegree < n := by
    dsimp only [r]
    rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
    omega
  have he (y : ℝ) : q.eval 1+(y-1)*r.eval y = q.eval y := by
    have h := congrArg (fun p : ℝ[X] ↦ p.eval y) (modByMonic_add_div q (X-C (1 : ℝ)))
    simpa only [modByMonic_X_sub_C_eq_C_eval, eval_add, eval_mul, eval_sub, eval_C, eval_X] using h
  calc
    _ = q.eval 1*(∫ y in (0 : ℝ)..1, (shiftedJacobi 1 0 n).eval y) -
        ∫ y in (0 : ℝ)..1, (1-y)*r.eval y*(shiftedJacobi 1 0 n).eval y := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop)]
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      linear_combination -(shiftedJacobi 1 0 n).eval y*he y
    _ = _ := by
      rw [integral_mul_shiftedJacobi_one_zero_eq_zero r hr, hi, sub_zero]
      ring

/-- The mixed Jacobi/Legendre edge integral is constant throughout the degree block. -/
theorem integral_shiftedJacobi_one_zero_mul_zero_zero (n k : ℕ) (hk : k ≤ n) :
    (∫ y in (0 : ℝ)..1, (shiftedJacobi 1 0 n).eval y*(shiftedJacobi 0 0 k).eval y) =
      1/((n : ℝ)+1) := by
  rw [integral_shiftedJacobi_one_zero_mul n _ ((natDegree_shiftedJacobi_le 0 0 k).trans hk),
    eval_shiftedJacobi_zero_left_one]

/-- Unweighted Legendre orthogonality in shifted Jacobi notation. -/
theorem integral_mul_shiftedJacobi_zero_zero (j k : ℕ) :
    (∫ y in (0 : ℝ)..1, (shiftedJacobi 0 0 j).eval y*(shiftedJacobi 0 0 k).eval y) =
      if j = k then 1/(2*(k : ℝ)+1) else 0 := by
  have h := integralInner_shiftedJacobi (0 : ℝ) 0 j k
    (hi := (hasFiniteMoments_jacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _)
  let g : IntegrableInput (unitJacobiMeasure 0 0) := ⟨fun x ↦ (shiftedJacobi 0 0 j).eval x * (shiftedJacobi 0 0 k).eval x, (hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _⟩
  have hg : Measurable g.val := by dsimp [g]; fun_prop
  have hd : (∫ x, g.val x ∂unitJacobiMeasure 0 0) = 2 *
      ∫ x in (0 : ℝ)..1, g.val x := by
    rw [integral_unitJacobiMeasure_subtype 0 0 g hg]
    simp only [unitJacobiWeight_apply, zero_add, Real.rpow_one, Real.rpow_zero,
      mul_one]
    rw [integral_const_mul, integral_subtype measurableSet_Ioo g.val,
      restrict_Ioo_eq_restrict_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  dsimp only [g] at hd
  rw [integralInner, hd] at h
  by_cases hj : j = k
  · subst j
    rw [integralInner, show (fun x ↦ (jacobi (0 : ℝ) 0 k).eval x*
      (jacobi (0 : ℝ) 0 k).eval x) = (fun x ↦ (jacobi (0 : ℝ) 0 k).eval x^2) by ext; ring,
      integral_sq_jacobi_zero_left (by norm_num)] at h
    norm_num only [zero_add, Real.rpow_one, add_zero] at h
    simp only [ite_true]
    linear_combination h/2
  · rw [integralInner, integral_mul_jacobi_eq_zero (by norm_num) (by norm_num) hj] at h
    simp only [ite_eq_right_iff.mpr (fun h ↦ (hj h).elim)]
    linarith

end Polynomial
namespace MvPolynomial
open Polynomial

/-- Restriction of a DLMF Proriol mode to the outer edge is a shifted Legendre mode. -/
theorem eval_proriol_outer_one (n k : ℕ) (y : ℝ) :
    eval (![1,y] : Fin 2 → ℝ) (proriol 0 0 0 n k) = (shiftedJacobi 0 0 k).eval y := by
  have h := eval_proriol_scaled 0 0 0 n k 1 y
  simpa only [one_mul, one_pow, mul_one, zero_add, eval_shiftedJacobi_zero_left_one] using h

end MvPolynomial
