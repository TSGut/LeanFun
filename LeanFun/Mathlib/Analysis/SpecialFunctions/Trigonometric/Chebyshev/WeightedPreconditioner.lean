/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.Normed.Lp.DegreeWeightedOperators
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.CoefficientPreconditioner
/-! # Weighted ultraspherical right preconditioning
Reference: Olver--Townsend (2013), Section 4.1. The positive-degree diagonal
is 1/(2^k k! n); the constant mode is 1/(2^k k!). This differs from the paper
only in the finitely many modes below the differentiation order.
-/
@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open ContinuousLinearMap

/-- Reciprocal-degree preconditioning in the weighted coefficient norm. -/
def weightedFirstOrderPreconditioner (s : ℕ) : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  lp.degreeWeightedDiagonal s firstOrderDiagonal zero_le_one norm_firstOrderDiagonal_le

/-- Reciprocal-degree decay gives compactness in each weighted space. -/
theorem isCompactOperator_weightedFirstOrderPreconditioner (s : ℕ) :
    IsCompactOperator (weightedFirstOrderPreconditioner s) :=
  lp.isCompactOperator_degreeWeightedDiagonal s _ _ _ tendsto_firstOrderDiagonal

/-- The weighted preconditioner has the same diagonal entries as on ordinary ℓ². -/
theorem weightedFirstOrderPreconditioner_apply (s : ℕ) (x : lp.DegreeWeightedL2 s) (n : ℕ) :
    (weightedFirstOrderPreconditioner s x).1 n = firstOrderDiagonal n * x.1 n :=
  lp.degreeWeightedDiagonal_apply s _ _ _ x n

/-- The positive normalization factor for derivative order k+1. -/
def ultrasphericalDerivativeScale (k : ℕ) : ℂ := (2 : ℂ)^k * (k.factorial : ℂ)

/-- The derivative normalization factor is nonzero. -/
theorem ultrasphericalDerivativeScale_ne_zero (k : ℕ) : ultrasphericalDerivativeScale k ≠ 0 := by
  unfold ultrasphericalDerivativeScale
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)

/-- Order k+1 right preconditioner, with reciprocal-degree scaling on positive modes. -/
def weightedUltrasphericalPreconditioner (s k : ℕ) :
    lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  (ultrasphericalDerivativeScale k)⁻¹ • weightedFirstOrderPreconditioner s

/-- The normalized right preconditioner is compact. -/
theorem isCompactOperator_weightedUltrasphericalPreconditioner (s k : ℕ) :
    IsCompactOperator (weightedUltrasphericalPreconditioner s k) := by
  change IsCompactOperator ((ultrasphericalDerivativeScale k)⁻¹ • ⇑(weightedFirstOrderPreconditioner s))
  exact (isCompactOperator_weightedFirstOrderPreconditioner s).smul _

/-- Positive derivative after right preconditioning. -/
def weightedPreconditionedDerivative (s k j : ℕ) :
    lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  (ultrasphericalDerivativeScale j / ultrasphericalDerivativeScale k) •
    (lp.degreeWeightedShiftLeft s)^(j + 1)

/-- The highest preconditioned derivative is the backward shift of the differential order. -/
theorem weightedPreconditionedDerivative_top (s k : ℕ) :
    weightedPreconditionedDerivative s k k = (lp.degreeWeightedShiftLeft s)^(k + 1) := by
  simp [weightedPreconditionedDerivative, ultrasphericalDerivativeScale_ne_zero]
end Polynomial.Chebyshev
