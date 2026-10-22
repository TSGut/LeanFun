/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Coordinates
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact polynomial moments on the unweighted Proriol triangle

Integration of monomials gives finite arithmetic formulas for polynomial
pairings. The triangle is `0 ≤ y ≤ x ≤ 1`, with unnormalized area measure.
Reference: DLMF 18.37.8, specialized to zero weight parameters.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- Exact integration of a monomial on the unweighted DLMF triangle. -/
theorem integral_monomial_proriolMeasure_zero (d : Fin 2 →₀ ℕ) (a : ℝ) :
    (∫ v, eval v (monomial d a) ∂proriolMeasure 0 0 0) =
      a / (((d 1 : ℝ)+1)*((d 0 : ℝ)+d 1+2)) := by
  rw [integral_proriolMeasure_density (by norm_num) (by norm_num) (by norm_num)]
  simp only [Real.rpow_zero, one_mul, eval_monomial]
  have he (x y : ℝ) : d.prod (fun i n ↦ (![x,y] : Fin 2 → ℝ) i ^ n) =
      x^(d 0)*y^(d 1) := by
    rw [Finsupp.prod_fintype]
    · simp
    · simp
  simp_rw [he, ← mul_assoc]
  have heq (x : Set.Ioo (0 : ℝ) 1) :
      (∫ y : Set.Ioo (0 : ℝ) (x : ℝ), a*(x : ℝ)^(d 0)*(y : ℝ)^(d 1)) =
      ∫ y in (0 : ℝ)..(x : ℝ), a*(x : ℝ)^(d 0)*y^(d 1) := by
    rw [integral_subtype measurableSet_Ioo (fun y : ℝ ↦ a*(x : ℝ)^(d 0)*y^(d 1)),
      restrict_Ioo_eq_restrict_Ioc, intervalIntegral.integral_of_le x.property.1.le]
  simp_rw [heq]
  rw [integral_subtype measurableSet_Ioo
    (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, a*x^(d 0)*y^(d 1)),
    restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp_rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
  calc
    _ = a / ((d 1 : ℝ)+1) * ∫ x in (0 : ℝ)..1, x^(d 0+d 1+1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [pow_add, pow_one]
      ring
    _ = _ := by
      rw [integral_pow]
      simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
      ring

/-- Finite coefficient formula for the integral, with no analytic operation. -/
def proriolTriangleMoment (p : MvPolynomial (Fin 2) ℝ) : ℝ :=
  ∑ d ∈ p.support, p.coeff d / (((d 1 : ℝ)+1)*((d 0 : ℝ)+d 1+2))

/-- The finite moment formula agrees with integration for every polynomial. -/
theorem integral_eval_proriolMeasure_zero (p : MvPolynomial (Fin 2) ℝ) :
    (∫ v, eval v p ∂proriolMeasure 0 0 0) = proriolTriangleMoment p := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum]
  rw [integral_finsetSum]
  · simp only [integral_monomial_proriolMeasure_zero, proriolTriangleMoment]
  · intro d _
    simpa only [map_one, mul_one] using
      (hasFiniteMoments_proriolMeasure (α := 0) (β := 0) (γ := 0)
        (by norm_num) (by norm_num) (by norm_num)).integrable_mul
          (monomial d (p.coeff d)) 1

/-- Polynomial pairings on the unweighted triangle are finite coefficient sums. -/
theorem integralInner_proriolMeasure_zero (p q : MvPolynomial (Fin 2) ℝ) :
    integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) p q (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) = proriolTriangleMoment (p*q) := by
  rw [integralInner, ← integral_eval_proriolMeasure_zero]
  simp only [map_mul]

/-- The squared norm is also given by the finite moment formula. -/
theorem integral_sq_proriolMeasure_zero (p : MvPolynomial (Fin 2) ℝ) :
    (∫ v, (eval v p)^2 ∂proriolMeasure 0 0 0) = proriolTriangleMoment (p^2) := by
  rw [← integral_eval_proriolMeasure_zero]
  simp only [map_pow]

/-- Exact finite-arithmetic coordinates in the unweighted Proriol basis. -/
theorem proriolDegreeBasis_repr_zero (N : ℕ)
    (p : restrictTotalDegree (Fin 2) ℝ N)
    (i : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (proriolDegreeBasis (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) N).repr p i =
      proriolTriangleMoment ((p : MvPolynomial (Fin 2) ℝ) *
        proriol 0 0 0 (i.1 0+i.1 1) (i.1 1)) /
      proriolTriangleMoment ((proriol 0 0 0 (i.1 0+i.1 1) (i.1 1))^2) := by
  rw [proriolDegreeBasis_repr, integralInner_proriolMeasure_zero,
    integral_sq_proriolMeasure_zero]

/-- The finite denominator in the Proriol coordinate formula is strictly positive. -/
theorem proriolTriangleMoment_sq_proriol_pos (n k : ℕ) :
    0 < proriolTriangleMoment ((proriol 0 0 0 n k)^2) := by
  rw [← integral_sq_proriolMeasure_zero]
  exact integral_sq_proriolMeasure_pos (by norm_num) (by norm_num) (by norm_num) n k

end MvPolynomial
