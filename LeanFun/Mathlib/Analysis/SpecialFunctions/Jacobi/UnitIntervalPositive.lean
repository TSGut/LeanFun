/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalSequence
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.NormBounds
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionSupport

/-! # Positive leading coefficients and diagonal affine Jacobi pairings
Reference: DLMF Table 18.3.1 and positive normalization of measure conversion.
-/

public section
namespace Polynomial

/-- Affine Jacobi polynomials retain positive leading coefficients. -/
theorem leadingCoeff_shiftedJacobi_pos {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    0 < (shiftedJacobi α β n).leadingCoeff := by
  have hd : (C (2 : ℝ) * X - 1).degree = 1 := by
    rw [degree_sub_eq_left_of_degree_lt (by simp)]
    simp
  have hn : (C (2 : ℝ) * X - 1).natDegree = 1 := natDegree_eq_of_degree_eq_some hd
  have hl : (C (2 : ℝ) * X - 1).leadingCoeff = 2 := by
    rw [leadingCoeff_sub_of_degree_lt (by simp)]
    simp
  rw [shiftedJacobi, leadingCoeff_comp (by rw [hn]; decide), hl]
  have hp : 0 < (jacobi α β n).leadingCoeff := by
    have hdj : (jacobi α β n).natDegree = n := (jacobiSequence hα hβ).natDegree_eq n
    rw [leadingCoeff, hdj]
    exact coeff_jacobi_self_pos hα hβ n
  positivity

/-- Same-degree pairings against any other admissible affine Jacobi family are positive. -/
theorem integralInner_shiftedJacobi_diag_pos {α β α' β' : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hα' : -1 < α') (hβ' : -1 < β') (n : ℕ) :
    0 < integralInner (unitJacobiMeasure α' β') (IntegrablePair.of (unitJacobiMeasure α' β') (shiftedJacobi α β n) (shiftedJacobi α' β' n)) := by
  apply (isOrthogonal_shiftedJacobiSequence hα' hβ').integralInner_pos_of_leadingCoeff_pos
    (hasFiniteMoments_unitJacobiMeasure hα' hβ')
    ((shiftedJacobiSequence hα hβ).natDegree_eq n)
    (leadingCoeff_shiftedJacobi_pos hα hβ n) (leadingCoeff_shiftedJacobi_pos hα' hβ' n)
  simp only [shiftedJacobiSequence_apply]
  rw [integralInner_shiftedJacobi α' β' n n
    (hi := (hasFiniteMoments_jacobiMeasure hα' hβ').integrable_mul _ _), integralInner_self]
  exact integral_sq_jacobi_pos hα' hβ' n

end Polynomial
