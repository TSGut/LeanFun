/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.PartialWeightedDerivative
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DerivativeSupport

/-! # Two-diagonal partial weighted differentiation
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.4.
-/

public section
namespace Polynomial

/-- Weighting at the external singularity does not increase polynomial degree. -/
theorem natDegree_semiclassicalJacobiCWeightedDerivativeMap_le (t γ : ℝ) (p : ℝ[X]) :
    (semiclassicalJacobiCWeightedDerivativeMap t γ p).natDegree ≤ p.natDegree := by
  change ((C t-X)*p.derivative-C (γ+1)*p).natDegree ≤ _
  have ht : (C t-X).natDegree ≤ 1 := by compute_degree
  have hc : (C (γ+1)).natDegree ≤ 0 := by simp
  by_cases hp : p.natDegree=0
  · rw [derivative_of_natDegree_zero hp, mul_zero, zero_sub, natDegree_neg]
    exact natDegree_mul_le.trans (by omega)
  · have hd := natDegree_derivative_le p
    exact (natDegree_sub_le _ _).trans (max_le
      (natDegree_mul_le.trans (by omega)) (natDegree_mul_le.trans (by omega)))

/-- The partial adjoint increases degree by at most one. -/
theorem natDegree_semiclassicalJacobi_cAdjoint_le (α β : ℝ) (p : ℝ[X]) :
    (X*(1-X)*p.derivative+(C (α+1)*(1-X)-C (β+1)*X)*p).natDegree ≤ p.natDegree+1 := by
  have hs : (X*(1-X) : ℝ[X]).natDegree ≤ 2 := by compute_degree
  have ht : (C (α+1)*(1-X)-C (β+1)*X).natDegree ≤ 1 := by compute_degree
  by_cases hp : p.natDegree=0
  · rw [derivative_of_natDegree_zero hp, mul_zero, zero_add]
    exact natDegree_mul_le.trans (by omega)
  · have hd := natDegree_derivative_le p
    exact (natDegree_add_le _ _).trans (max_le
      (natDegree_mul_le.trans (by omega)) (natDegree_mul_le.trans (by omega)))

/-- Only rows n-1 and n can occur in column n. -/
theorem integralInner_semiclassicalJacobi_cWeightedDerivative_eq_zero {t α β γ : ℝ}
    (ht : 1<t) (hα : -1<α) (hβ : -1<β)
    (hα1 : -1<α+1) (hβ1 : -1<β+1) (n j : ℕ)
    (hgap : n<j ∨ j+1<n) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) γ) (semiclassicalJacobiCWeightedDerivativeMap t γ
        (semiclassicalJacobiSequence ht hα hβ (γ+1) n)) (semiclassicalJacobiSequence ht hα1 hβ1 γ j)) = 0 := by
  rcases hgap with h | h
  · apply (semiclassicalJacobiSequence_spec ht hα1 hβ1 γ).1.integralInner_eq_zero_of_degree_lt
      (hasFiniteMoments_semiclassicalJacobiMeasure ht hα1 hβ1)
    apply degree_le_natDegree.trans_lt
    have hd := natDegree_semiclassicalJacobiCWeightedDerivativeMap_le t γ
      (semiclassicalJacobiSequence ht hα hβ (γ+1) n)
    rw [Sequence.natDegree_eq] at hd
    exact_mod_cast hd.trans_lt h
  · rw [integralInner_semiclassicalJacobi_cWeightedDerivative ht hα hβ, integralInner_comm]
    suffices hz : integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β (γ+1)) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β (γ+1)) (X*(1-X)*(semiclassicalJacobiSequence ht hα1 hβ1 γ j).derivative+
          (C (α+1)*(1-X)-C (β+1)*X)*semiclassicalJacobiSequence ht hα1 hβ1 γ j) (semiclassicalJacobiSequence ht hα hβ (γ+1) n)) = 0 by rw [hz, neg_zero]
    apply (semiclassicalJacobiSequence_spec ht hα hβ (γ+1)).1.integralInner_eq_zero_of_degree_lt
      (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
    apply degree_le_natDegree.trans_lt
    have hd := natDegree_semiclassicalJacobi_cAdjoint_le α β
      (semiclassicalJacobiSequence ht hα1 hβ1 γ j)
    rw [Sequence.natDegree_eq] at hd
    exact_mod_cast hd.trans_lt h

end Polynomial
