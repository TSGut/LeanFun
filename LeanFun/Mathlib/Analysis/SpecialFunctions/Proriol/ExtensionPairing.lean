/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ExtensionMoments
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ExtensionEntries
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalDensity
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Ring.GeomSum

/-! # Pairings of inner-coordinate extensions on the triangle

The unweighted triangle marginal in the inner coordinate has Jacobi weight
`1-y`. This is the reason extension of a shifted `(1,0)` Jacobi mode stays in
one total-degree block. Reference: Gutleb–Olver, arXiv:1906.03907, Section 3.1.
-/

public section
open MeasureTheory Polynomial
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- Orthogonality for shifted `(1,0)` modes with the unnormalized density. -/
theorem integral_mul_shiftedJacobi_one_zero_eq_zero {n : ℕ} (q : ℝ[X])
    (hq : q.natDegree < n) :
    (∫ y in (0 : ℝ)..1, (1-y)*q.eval y*(shiftedJacobi 1 0 n).eval y) = 0 := by
  have h := (isOrthogonal_shiftedJacobiSequence (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0)).integralInner_eq_zero_of_degree_lt
      (hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num))
      (degree_le_natDegree.trans_lt (by exact_mod_cast hq))
  change integralInner (unitJacobiMeasure 1 0) (IntegrablePair.of (unitJacobiMeasure 1 0) q (shiftedJacobi 1 0 n) (h := (hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _)) = 0 at h
  let g : IntegrableInput (unitJacobiMeasure 1 0) := ⟨fun x ↦ q.eval x * (shiftedJacobi 1 0 n).eval x, (hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _⟩
  have hg : Measurable g.val := by dsimp [g]; fun_prop
  have hd : (∫ x, g.val x ∂unitJacobiMeasure 1 0) = 4 *
      ∫ x in (0 : ℝ)..1, (1-x) * g.val x := by
    rw [integral_unitJacobiMeasure_subtype 1 0 g hg]
    simp only [unitJacobiWeight_apply, add_zero, Real.rpow_one, Real.rpow_zero,
      mul_one, mul_assoc]
    norm_num only [one_add_one_eq_two, Real.rpow_two]
    rw [integral_const_mul, integral_subtype measurableSet_Ioo (fun x : ℝ ↦ (1-x)*g.val x),
      restrict_Ioo_eq_restrict_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  dsimp only [g] at hd
  rw [integralInner, hd] at h
  have he : (∫ y in (0 : ℝ)..1, (1-y)*(q.eval y*(shiftedJacobi 1 0 n).eval y)) = 0 := by
    nlinarith [h]
  simpa only [mul_assoc] using he

end Polynomial
namespace MvPolynomial

/-- Pairing an extended polynomial with a triangle monomial reduces to one
ordinary integral. The formula includes the exact triangle marginal factor. -/
theorem integralInner_extendY_monomial (p : ℝ[X]) (d : Fin 2 →₀ ℕ) (a : ℝ) :
    integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) (triangleExtendY p) (monomial d a) (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) =
      a/((d 0 : ℝ)+1) * ∫ y in (0 : ℝ)..1, p.eval y*y^(d 1)*(1-y^(d 0+1)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add]
    rw [integralInner_add_left
      (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)), hp, hq]
    simp only [Polynomial.eval_add, add_mul]
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    ring
  | monomial n b =>
    have hm : triangleExtendY (Polynomial.monomial n b) * monomial d a =
        monomial (Finsupp.single 1 n+d) (b*a) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      simp only [triangleExtendY, Polynomial.aeval_C, Polynomial.aeval_X]
      change C b*X 1^n*monomial d a = _
      rw [MvPolynomial.C_mul_X_pow_eq_monomial, monomial_mul_monomial]
    rw [integralInner]
    simp_rw [← map_mul]
    rw [hm, integral_monomial_proriolMeasure_zero]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
      zero_add, Nat.cast_add, Polynomial.eval_monomial]
    have he : (∫ y in (0 : ℝ)..1, b*y^n*y^(d 1)*(1-y^(d 0+1))) =
        b*((1/((n : ℝ)+d 1+1))-(1/((n : ℝ)+d 1+d 0+2))) := by
      calc
        _ = b*((∫ y in (0 : ℝ)..1, y^(n+d 1)) -
            ∫ y in (0 : ℝ)..1, y^(n+d 1+d 0+1)) := by
          rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
            (by apply Continuous.intervalIntegrable; fun_prop), ← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro y _
          dsimp only
          simp only [pow_add, pow_one]
          ring
        _ = _ := by
          rw [integral_pow, integral_pow]
          simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one]
          ring
    rw [he]
    have h0 : (d 0 : ℝ)+1 ≠ 0 := by positivity
    have h1 : (n : ℝ)+d 1+1 ≠ 0 := by positivity
    have h2 : (n : ℝ)+d 1+d 0+2 ≠ 0 := by positivity
    have h3 : (d 0 : ℝ)+((n : ℝ)+d 1)+2 ≠ 0 := by positivity
    field_simp
    ring

/-- Extending a shifted `(1,0)` mode makes it orthogonal to every lower
triangle degree, not merely to the inner-degree-zero modes. -/
theorem integralInner_extendY_shiftedJacobi_eq_zero {n : ℕ}
    (q : MvPolynomial (Fin 2) ℝ) (hq : q.totalDegree < n) :
    integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) (triangleExtendY (shiftedJacobi 1 0 n)) q (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) = 0 := by
  classical
  have hm (d : Fin 2 →₀ ℕ) (a : ℝ) (hd : d 0+d 1 < n) :
      integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) (triangleExtendY (shiftedJacobi 1 0 n)) (monomial d a) (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) = 0 := by
    let r : ℝ[X] := Polynomial.X^(d 1) * ∑ i ∈ Finset.range (d 0+1), Polynomial.X^i
    have hr : r.natDegree ≤ d 0+d 1 := by
      apply Polynomial.natDegree_mul_le.trans
      rw [Polynomial.natDegree_X_pow]
      have hs : (∑ i ∈ Finset.range (d 0+1), (Polynomial.X : ℝ[X])^i).natDegree ≤ d 0 := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro i hi
        simpa only [Polynomial.natDegree_X_pow] using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      omega
    rw [integralInner_extendY_monomial]
    have he : (∫ y in (0 : ℝ)..1, (shiftedJacobi 1 0 n).eval y*y^(d 1)*(1-y^(d 0+1))) =
        ∫ y in (0 : ℝ)..1, (1-y)*r.eval y*(shiftedJacobi 1 0 n).eval y := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      simp only [r, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_finsetSum]
      linear_combination -(shiftedJacobi 1 0 n).eval y*y^(d 1)*geom_sum_mul_neg y (d 0+1)
    rw [he, integral_mul_shiftedJacobi_one_zero_eq_zero r (hr.trans_lt hd), mul_zero]
  let B := integralBilinForm (proriolMeasure 0 0 0)
    (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num))
  change B (triangleExtendY (shiftedJacobi 1 0 n)) q = 0
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply hm
  have h := le_totalDegree hd
  rw [sum_exponents_fin_two] at h
  omega

end MvPolynomial
