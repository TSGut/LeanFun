/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitInterval
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Recurrence

/-! # The shifted Jacobi orthogonal sequence
Affine transport retains degree and orthogonality, for use in DLMF 18.37.7.
-/

@[expose] public section
namespace Polynomial

/-- The Jacobi sequence in the affine unit-interval coordinate. -/
noncomputable def shiftedJacobiSequence {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    Sequence ℝ where
  elems' := shiftedJacobi α β
  degree_eq' n := by
    have hd : (C (2 : ℝ) * X - 1).degree = 1 := by
      rw [degree_sub_eq_left_of_degree_lt (by simp)]
      simp
    rw [shiftedJacobi, degree_comp (by rw [hd]; norm_num),
      degree_jacobi_of_neg_one_lt hα hβ, hd, mul_one]

@[simp] theorem shiftedJacobiSequence_apply {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    shiftedJacobiSequence hα hβ n = shiftedJacobi α β n := rfl

/-- Shifted Jacobi polynomials are orthogonal for the transported measure. -/
theorem isOrthogonal_shiftedJacobiSequence {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobiSequence hα hβ).IsOrthogonal (unitJacobiMeasure α β) where
  integrable n m := (hasFiniteMoments_unitJacobiMeasure hα hβ).integrable_mul _ _
  orthogonal n m hnm := by
    change integralInner (unitJacobiMeasure α β) (IntegrablePair.of (unitJacobiMeasure α β) (shiftedJacobi α β n) (shiftedJacobi α β m)) = 0
    rw [integralInner_shiftedJacobi α β n m (hi := (hasFiniteMoments_jacobiMeasure hα hβ).integrable_mul _ _), integralInner, integral_mul_jacobi_eq_zero hα hβ hnm]

end Polynomial
