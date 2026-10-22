/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Orthogonality
public import LeanFun.Mathlib.RingTheory.Polynomial.Legendre.Basic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Uniqueness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Legendre orthogonality and squared norms

The weight is one on `[-1,1]`. We use restriction to `(-1,1]`, which agrees
with the closed interval for Lebesgue integration. Reference: DLMF Table 18.3.1.
-/

public section

open MeasureTheory Set

namespace Polynomial

/-- The unit Legendre weight, restricted to `(-1,1]` (DLMF Table 18.3.1). -/
@[expose] noncomputable def legendreMeasure : Measure ℝ := volume.restrict (Ioc (-1) 1)

/-- Every polynomial square is integrable for the Legendre weight (DLMF Table 18.3.1). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_legendreMeasure : HasFiniteMoments legendreMeasure := by
  intro p
  exact (p.continuous.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The unit Legendre measure is the zero-parameter Jacobi measure
(DLMF Table 18.3.1). -/
theorem legendreMeasure_eq_jacobiMeasure : legendreMeasure = jacobiMeasure 0 0 := by
  have h : jacobiMeasure 0 0 = (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
      (fun _ ↦ 1) := by
    apply openIntervalWeightMeasure_eq _ _ _ _ measurable_const
    intro x
    simp [jacobiWeight]
    rfl
  simpa [legendreMeasure, restrict_Ioo_eq_restrict_Ioc] using h.symm

/-- Distinct Legendre polynomials are orthogonal on `[-1,1]` (DLMF Table 18.3.1). -/
theorem integral_mul_legendre_eq_zero {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (legendre ℝ m).eval x * (legendre ℝ n).eval x = 0 := by
  have h := integral_mul_jacobi_eq_zero (α := 0) (β := 0) (by norm_num) (by norm_num) hmn
  simpa [← legendre_eq_jacobi, ← legendreMeasure_eq_jacobiMeasure, legendreMeasure,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] using h

/-- The Legendre sequence is orthogonal for its unit weight (DLMF Table 18.3.1). -/
theorem isOrthogonal_legendreSequence : (legendreSequence ℝ).IsOrthogonal legendreMeasure where
  integrable m n := hasFiniteMoments_legendreMeasure.integrable_mul _ _
  orthogonal m n hmn := by
    simpa only [legendreSequence_apply, legendreMeasure,
      intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] using
      integral_mul_legendre_eq_zero hmn

/-- Legendre polynomials are orthogonal to every polynomial of lower degree
(DLMF 18.2(i)). -/
theorem integral_mul_legendre_eq_zero_of_degree_lt {p : ℝ[X]} {n : ℕ}
    (hp : p.degree < n) : ∫ x in (-1 : ℝ)..1, p.eval x * (legendre ℝ n).eval x = 0 := by
  have h := isOrthogonal_legendreSequence.integralInner_eq_zero_of_degree_lt
    hasFiniteMoments_legendreMeasure hp
  simpa only [integralInner, legendreMeasure, legendreSequence_apply,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] using h

private theorem degree_derivative_legendre_succ_sub (n : ℕ) :
    (derivative (legendre ℝ (n + 1)) - C (2 * (n : ℝ) + 1) * legendre ℝ n).degree < n := by
  have hd : (derivative (legendre ℝ (n + 1))).degree ≤ n := by
    rw [degree_derivative (by simp), natDegree_legendre]
    simp
  have hc : (C (2 * (n : ℝ) + 1) * legendre ℝ n).degree = n := by
    rw [degree_C_mul (by positivity), degree_legendre]
  have hr : (derivative (legendre ℝ (n + 1)) - C (2 * (n : ℝ) + 1) * legendre ℝ n).degree ≤ n :=
    (degree_sub_le _ _).trans (max_le hd hc.le)
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rcases eq_or_lt_of_le hk with rfl | hnk
  · rw [coeff_sub, coeff_C_mul, coeff_derivative_legendre_succ, sub_self]
  · exact coeff_eq_zero_of_degree_lt (hr.trans_lt (by exact_mod_cast hnk))

/-- The squared Legendre norm for the unit weight is `2/(2n+1)`
(DLMF Table 18.3.1). -/
theorem integral_sq_legendre (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre ℝ n).eval x ^ 2 = 2 / (2 * (n : ℝ) + 1) := by
  have hd : (derivative (legendre ℝ n)).degree < (n + 1 : ℕ) := by
    exact degree_derivative_le.trans_lt (by rw [degree_legendre]; exact_mod_cast Nat.lt_succ_self n)
  have hz := integral_mul_legendre_eq_zero_of_degree_lt hd
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (legendre ℝ n).continuous.continuousOn (legendre ℝ (n + 1)).continuous.continuousOn
    (fun x _ ↦ (legendre ℝ n).hasDerivAt x)
    (fun x _ ↦ (legendre ℝ (n + 1)).hasDerivAt x)
    ((legendre ℝ n).derivative.continuous.intervalIntegrable (-1) 1)
    ((legendre ℝ (n + 1)).derivative.continuous.intervalIntegrable (-1) 1)
  have hboundary : (legendre ℝ n).eval 1 * (legendre ℝ (n + 1)).eval 1 -
      (legendre ℝ n).eval (-1) * (legendre ℝ (n + 1)).eval (-1) = 2 := by
    simp only [eval_legendre_one, eval_legendre_neg_one, pow_succ]
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [hboundary, hz, sub_zero] at hibp
  have hr := integral_mul_legendre_eq_zero_of_degree_lt (degree_derivative_legendre_succ_sub n)
  have hi₁ : IntervalIntegrable (fun x ↦ (derivative (legendre ℝ (n + 1))).eval x *
      (legendre ℝ n).eval x) volume (-1) 1 := by
    exact ((legendre ℝ (n + 1)).derivative.continuous.mul (legendre ℝ n).continuous).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun x ↦ (2 * (n : ℝ) + 1) * (legendre ℝ n).eval x ^ 2)
      volume (-1) 1 := by
    exact (continuous_const.mul ((legendre ℝ n).continuous.pow 2)).intervalIntegrable _ _
  simp only [eval_sub, eval_mul, eval_C, sub_mul, mul_assoc, ← pow_two] at hr
  rw [intervalIntegral.integral_sub hi₁ hi₂, intervalIntegral.integral_const_mul] at hr
  have he : (∫ x in (-1 : ℝ)..1, (legendre ℝ n).eval x *
      (derivative (legendre ℝ (n + 1))).eval x) =
      ∫ x in (-1 : ℝ)..1, (derivative (legendre ℝ (n + 1))).eval x * (legendre ℝ n).eval x := by
    congr 1
    funext x
    ring
  rw [he] at hibp
  apply (eq_div_iff (by positivity : 2 * (n : ℝ) + 1 ≠ 0)).2
  nlinarith

/-- The diagonal norm also uses the Legendre measure directly (DLMF Table 18.3.1). -/
theorem integral_sq_legendre_measure (n : ℕ) :
    ∫ x, (legendre ℝ n).eval x ^ 2 ∂legendreMeasure = 2 / (2 * (n : ℝ) + 1) := by
  simpa only [legendreMeasure, intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
    using integral_sq_legendre n

/-- The complete Legendre integral pairing (DLMF Table 18.3.1). -/
theorem integral_mul_legendre (m n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre ℝ m).eval x * (legendre ℝ n).eval x =
      if m = n then 2 / (2 * (n : ℝ) + 1) else 0 := by
  by_cases h : m = n
  · subst m
    simpa only [ite_true, ← pow_two] using integral_sq_legendre n
  · rw [ite_eq_right h]
    exact integral_mul_legendre_eq_zero h

/-- The complete pairing for the Legendre measure (DLMF Table 18.3.1). -/
theorem integral_mul_legendre_measure (m n : ℕ) :
    ∫ x, (legendre ℝ m).eval x * (legendre ℝ n).eval x ∂legendreMeasure =
      if m = n then 2 / (2 * (n : ℝ) + 1) else 0 := by
  simpa only [legendreMeasure, intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
    using integral_mul_legendre m n

end Polynomial
