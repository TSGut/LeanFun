/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.IntegrationByParts
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Sequence
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Uniqueness
import Mathlib.Tactic.ComputeDegree

/-! # Two-diagonal differentiation in the semiclassical hierarchy
Differentiation from (alpha,beta,gamma) to (alpha+1,beta+1,gamma+1) has only
rows n-1 and n-2 in column n. Reference: the Pearson argument for semiclassical
Jacobi hierarchies, Papadopoulos–Gutleb–Slevinsky–Olver, Section 3.4.
-/

public section
namespace Polynomial

/-- The polynomial adjoint of differentiation raises degree by at most two. -/
theorem natDegree_semiclassicalJacobi_adjoint_le (t α β γ : ℝ) (q : ℝ[X]) :
    (semiclassicalJacobiSigma t*q.derivative + semiclassicalJacobiTau t α β γ*q).natDegree ≤
      q.natDegree+2 := by
  have hs : (semiclassicalJacobiSigma t).natDegree ≤ 3 := by
    unfold semiclassicalJacobiSigma
    compute_degree
  have ht : (semiclassicalJacobiTau t α β γ).natDegree ≤ 2 := by
    unfold semiclassicalJacobiTau
    compute_degree
  by_cases hq : q.natDegree = 0
  · rw [derivative_of_natDegree_zero hq, mul_zero, zero_add]
    exact natDegree_mul_le.trans (by omega)
  · have hd := natDegree_derivative_le q
    exact (natDegree_add_le _ _).trans (max_le
      (natDegree_mul_le.trans (by omega)) (natDegree_mul_le.trans (by omega)))

/-- Only the first two upper diagonals survive in the shifted derivative pairing. -/
theorem integralInner_semiclassicalJacobi_derivative_eq_zero {t α β γ : ℝ}
    (ht : 1 < t) (hα : -1 < α) (hβ : -1 < β)
    (hα1 : -1 < α+1) (hβ1 : -1 < β+1) (n j : ℕ)
    (hgap : n ≤ j ∨ j+2 < n) :
    integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) (γ+1)) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ (α+1) (β+1) (γ+1)) (semiclassicalJacobiSequence ht hα hβ γ n).derivative (semiclassicalJacobiSequence ht hα1 hβ1 (γ+1) j)) = 0 := by
  let P := semiclassicalJacobiSequence ht hα hβ γ
  let Q := semiclassicalJacobiSequence ht hα1 hβ1 (γ+1)
  rcases hgap with h | h
  · by_cases hn : n=0
    · have hp : (P n).natDegree = 0 := by simp [hn]
      simp only [integralInner]
      rw [derivative_of_natDegree_zero hp]
      simp
    · apply (semiclassicalJacobiSequence_spec ht hα1 hβ1 (γ+1)).1.integralInner_eq_zero_of_degree_lt
        (hasFiniteMoments_semiclassicalJacobiMeasure ht hα1 hβ1)
      apply degree_le_natDegree.trans_lt
      have hd := natDegree_derivative_lt (p := P n) (by simpa using hn)
      exact_mod_cast hd.trans_le (by simpa using h)
  · rw [integralInner_semiclassicalJacobi_derivative ht hα hβ, integralInner_comm]
    have hz : integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ) (semiclassicalJacobiSigma t*(Q j).derivative + semiclassicalJacobiTau t α β γ*Q j) (P n)) = 0 := by
      apply (semiclassicalJacobiSequence_spec ht hα hβ γ).1.integralInner_eq_zero_of_degree_lt
        (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
      apply degree_le_natDegree.trans_lt
      have hd := natDegree_semiclassicalJacobi_adjoint_le t α β γ (Q j)
      rw [Q.natDegree_eq] at hd
      exact_mod_cast hd.trans_lt h
    rw [hz, neg_zero]

end Polynomial
