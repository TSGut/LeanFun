/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalDensity
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalSequence
import Mathlib.Topology.Algebra.Polynomial

/-! # Integer modifications of affine Jacobi measures
The affine mass factor is retained explicitly. Reference: DLMF Table 18.3.1.
-/

public section
open MeasureTheory Set
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- Integer shifts of both parameters give the corresponding polynomial density. -/
theorem integral_unitJacobiMeasure_add_nat (α β : ℝ) (a b : ℕ)
    (p : {p : ℝ[X] //
      Integrable (fun x ↦ p.eval x) (unitJacobiMeasure (α+a) (β+b)) ∧
      Integrable (fun x ↦ ((1-X)^a*X^b*p).eval x) (unitJacobiMeasure α β)}) :
    ∫ x, p.val.eval x ∂unitJacobiMeasure (α+a) (β+b) =
      (2 : ℝ)^(a+b) * ∫ x, ((1-X)^a*X^b*p.val).eval x ∂unitJacobiMeasure α β := by
  rw [integral_unitJacobiMeasure_subtype _ _ ⟨_,p.property.1⟩ (by dsimp only; fun_prop),
    integral_unitJacobiMeasure_subtype _ _ ⟨_,p.property.2⟩ (by dsimp only; fun_prop),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [unitJacobiWeight_apply, unitJacobiWeight_apply]
  have hc : (2 : ℝ)^(α+a+(β+b)+1) = (2 : ℝ)^(a+b) * (2 : ℝ)^(α+β+1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [hc, Real.rpow_add (by linarith [x.property.2] : 0 < 1-(x : ℝ)),
    Real.rpow_natCast, Real.rpow_add x.property.1, Real.rpow_natCast]
  simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_X]
  ring

/-- Pairing version of simultaneous affine Jacobi parameter raising. -/
theorem integralInner_unitJacobiMeasure_add_nat (α β : ℝ) (a b : ℕ) (p q : ℝ[X])
    (hi : Integrable (fun x => p.eval x*q.eval x) (unitJacobiMeasure (α+a) (β+b)) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hj : Integrable (fun x => ((1-X)^a*X^b*p).eval x*q.eval x) (unitJacobiMeasure α β) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (unitJacobiMeasure (α+a) (β+b)) (IntegrablePair.of (unitJacobiMeasure (α+a) (β+b)) p q) =
      (2 : ℝ)^(a+b) * integralInner (unitJacobiMeasure α β) (IntegrablePair.of (unitJacobiMeasure α β) ((1-X)^a*X^b*p) q) := by
  have he := integral_unitJacobiMeasure_add_nat α β a b ⟨p*q,
    by simpa only [eval_mul] using hi,
    by simpa only [eval_mul, mul_assoc] using hj⟩
  simpa only [integralInner, eval_mul, mul_assoc] using he

/-- Mixed shifted Jacobi pairings have the finite modification bandwidth. -/
theorem integralInner_shiftedJacobi_add_nat_eq_zero {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (a b k j : ℕ) (hgap : k < j ∨ j+(a+b) < k) :
    integralInner (unitJacobiMeasure (α+a) (β+b)) (IntegrablePair.of (unitJacobiMeasure (α+a) (β+b)) (shiftedJacobi α β k) (shiftedJacobi (α+a) (β+b) j) (h := (hasFiniteMoments_unitJacobiMeasure (by have := Nat.cast_nonneg (α := ℝ) a; linarith) (by have := Nat.cast_nonneg (α := ℝ) b; linarith)).integrable_mul _ _)) = 0 := by
  have hαa : -1 < α+a := by linarith [Nat.cast_nonneg (α := ℝ) a]
  have hβb : -1 < β+b := by linarith [Nat.cast_nonneg (α := ℝ) b]
  rcases hgap with h | h
  · apply (isOrthogonal_shiftedJacobiSequence hαa hβb).integralInner_eq_zero_of_degree_lt
      (hasFiniteMoments_unitJacobiMeasure hαa hβb)
    exact degree_le_natDegree.trans_lt (by
      exact_mod_cast (natDegree_shiftedJacobi_le α β k).trans_lt h)
  · rw [integralInner_comm, integralInner_unitJacobiMeasure_add_nat α β a b _ _
      (hi := (hasFiniteMoments_unitJacobiMeasure hαa hβb).integrable_mul _ _)
      (hj := (hasFiniteMoments_unitJacobiMeasure hα hβ).integrable_mul _ _)]
    apply mul_eq_zero_of_right
    apply (isOrthogonal_shiftedJacobiSequence hα hβ).integralInner_eq_zero_of_degree_lt
      (hasFiniteMoments_unitJacobiMeasure hα hβ)
    apply degree_le_natDegree.trans_lt
    have hpow : ((1-X : ℝ[X])^a).natDegree ≤ a := by
      rw [natDegree_pow]
      have hd : (1-X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
      simpa using Nat.mul_le_mul_left a hd
    have hd := natDegree_mul_le (p := (1-X)^a) (q := (X^b : ℝ[X]))
    have hd' := natDegree_mul_le (p := (1-X)^a*X^b) (q := shiftedJacobi (α+a) (β+b) j)
    have hj := natDegree_shiftedJacobi_le (α+a) (β+b) j
    simp only [natDegree_X_pow] at hd
    have hdeg : (((1-X)^a*X^b)*shiftedJacobi (α+a) (β+b) j).natDegree ≤ j+(a+b) := by omega
    exact_mod_cast hdeg.trans_lt h

end Polynomial
