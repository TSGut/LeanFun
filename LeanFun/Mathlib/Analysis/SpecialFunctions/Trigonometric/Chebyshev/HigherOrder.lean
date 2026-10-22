/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.WeightedUltraspherical
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.WeightedPreconditioner
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.DerivativeCoordinates
public import LeanFun.Mathlib.Analysis.Normed.Lp.DegreeWeightedBorder
public import LeanFun.Mathlib.Analysis.Normed.Lp.DegreeWeightedFiniteSection
/-! # Higher-order polynomial ultraspherical systems
Normalized order k+1 equations with polynomial lower-order coefficients and
bounded preconditioned boundary rows give compact perturbations of the identity.
Reference: Olver--Townsend (2013), Section 4.1.
-/
@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open ContinuousLinearMap Filter
open scoped Topology

/-- Preconditioned derivatives agree with every polynomial derivative in its natural basis. -/
theorem weightedPreconditionedDerivative_coefficient (s k j : ℕ)
    (v : lp.DegreeWeightedL2 s) (p : ℝ[X])
    (hv : weightedUltrasphericalPreconditioner s k v = chebyshevBasis.degreeWeightedCoefficient s p) :
    weightedPreconditionedDerivative s k j v =
      (ultrasphericalBasis (j + 1)).degreeWeightedCoefficient s ((derivative ^ (j + 1)) p) := by
  apply Subtype.ext
  funext i
  change (ultrasphericalDerivativeScale j / ultrasphericalDerivativeScale k) *
    (((lp.degreeWeightedShiftLeft s)^(j + 1)) v).1 i =
      ((ultrasphericalBasis (j + 1)).repr ((derivative ^ (j + 1)) p) i : ℂ)
  rw [lp.degreeWeightedShiftLeft_pow_apply, ultraspherical_derivative_coordinate]
  have h := congrArg (fun w : lp.DegreeWeightedL2 s ↦ w.1 (i + j + 1)) hv
  change (ultrasphericalDerivativeScale k)⁻¹ *
    (weightedFirstOrderPreconditioner s v).1 (i + j + 1) =
    (chebyshevBasis.repr p (i + j + 1) : ℂ) at h
  rw [weightedFirstOrderPreconditioner_apply] at h
  push_cast
  rw [← h, firstOrderDiagonal_succ]
  simp only [ultrasphericalDerivativeScale]
  push_cast
  have hn : (i : ℂ) + j + 1 ≠ 0 := by exact_mod_cast (show i + j + 1 ≠ 0 by omega)
  rw [show i + (j + 1) = i + j + 1 by omega]
  field_simp

/-- The zeroth-order term raised to the final ultraspherical level. -/
def weightedUltrasphericalZeroTerm (s k : ℕ) (a : ℝ[X]) :
    lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  (weightedPositiveRaise s 0 k).comp ((weightedChebyshevConversion s).comp
    ((weightedChebyshevPolynomialMultiplier s a).comp (weightedUltrasphericalPreconditioner s k)))

/-- The zeroth-order term is compact through right preconditioning. -/
theorem isCompactOperator_weightedUltrasphericalZeroTerm (s k : ℕ) (a : ℝ[X]) :
    IsCompactOperator (weightedUltrasphericalZeroTerm s k a) :=
  (((isCompactOperator_weightedUltrasphericalPreconditioner s k).clm_comp
    (weightedChebyshevPolynomialMultiplier s a)).clm_comp
      (weightedChebyshevConversion s)).clm_comp (weightedPositiveRaise s 0 k)

/-- A positive lower-order term raised to the final ultraspherical level. -/
def weightedUltrasphericalPositiveTerm (s k : ℕ) (j : Fin k) (a : ℝ[X]) :
    lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  (weightedPositiveRaise s j (k - j)).comp
    ((weightedPositivePolynomialMultiplier s j a).comp (weightedPreconditionedDerivative s k j))

set_option maxHeartbeats 800000 in
/-- Each positive lower-order term contains a compact conversion. -/
theorem isCompactOperator_weightedUltrasphericalPositiveTerm (s k : ℕ) (j : Fin k) (a : ℝ[X]) :
    IsCompactOperator (weightedUltrasphericalPositiveTerm s k j a) := by
  have h : k - j = (k - j - 1) + 1 := by omega
  have hc := (isCompactOperator_weightedPositiveRaise s j (k - j - 1)).comp_clm
    ((weightedPositivePolynomialMultiplier s j a).comp (weightedPreconditionedDerivative s k j))
  rw [← h] at hc
  exact hc

/-- The sum of all preconditioned lower-order polynomial terms. -/
def weightedUltrasphericalLowerTerms (s k : ℕ) (a₀ : ℝ[X]) (a : Fin k → ℝ[X]) :
    lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  weightedUltrasphericalZeroTerm s k a₀ + ∑ j, weightedUltrasphericalPositiveTerm s k j (a j)

/-- The preconditioned lower-order differential operator is compact. -/
theorem isCompactOperator_weightedUltrasphericalLowerTerms (s k : ℕ)
    (a₀ : ℝ[X]) (a : Fin k → ℝ[X]) :
    IsCompactOperator (weightedUltrasphericalLowerTerms s k a₀ a) := by
  apply (isCompactOperator_weightedUltrasphericalZeroTerm s k a₀).add
  have h (t : Finset (Fin k)) :
      IsCompactOperator (∑ j ∈ t, weightedUltrasphericalPositiveTerm s k j (a j) :
        lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) := by
    induction t using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero : IsCompactOperator
        (0 : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s))
    | @insert j t hj ih =>
      rw [Finset.sum_insert hj]
      exact (isCompactOperator_weightedUltrasphericalPositiveTerm s k j (a j)).add ih
  exact h Finset.univ

/-- The bordered polynomial differential operator minus the identity. -/
def weightedUltrasphericalRemainder (s k : ℕ) (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s)
    (a₀ : ℝ[X]) (a : Fin k → ℝ[X]) : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  lp.degreeWeightedBorderedRemainder s (k + 1) B (weightedUltrasphericalLowerTerms s k a₀ a)

/-- The higher-order bordered polynomial system is identity plus compact. -/
theorem isCompactOperator_weightedUltrasphericalRemainder (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X]) :
    IsCompactOperator (weightedUltrasphericalRemainder s k B a₀ a) :=
  lp.isCompactOperator_degreeWeightedBorderedRemainder s (k + 1) B _
    (isCompactOperator_weightedUltrasphericalLowerTerms s k a₀ a)

/-- Invertibility of the infinite system gives unique sufficiently large finite solves. -/
theorem eventually_existsUnique_weightedUltraspherical_system (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (hT : IsUnit (1 + weightedUltrasphericalRemainder s k B a₀ a)) :
    ∀ᶠ n in atTop, ∀ f : lp.DegreeWeightedL2 s, ∃! x : lp.DegreeWeightedL2 s,
      (∀ i, n ≤ i → x.1 i = 0) ∧
      (∀ i < n, ((1 + weightedUltrasphericalRemainder s k B a₀ a) x).1 i = f.1 i) :=
  lp.eventually_existsUnique_degreeWeighted_system s _
    (isCompactOperator_weightedUltrasphericalRemainder s k B a₀ a) hT

/-- Finite solves converge in the weighted preconditioned coefficient norm. -/
theorem tendsto_weightedUltraspherical_system_solution (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (hT : IsUnit (1 + weightedUltrasphericalRemainder s k B a₀ a)) (x : lp.DegreeWeightedL2 s) :
    Tendsto (fun n : Ring.InvertibleIndex
        (fun n ↦ liftedFiniteSection (lp.degreeWeightedProjection s n)
          (weightedUltrasphericalRemainder s k B a₀ a)) ↦
      Ring.inverseAt (fun n ↦ liftedFiniteSection (lp.degreeWeightedProjection s n)
          (weightedUltrasphericalRemainder s k B a₀ a)) n
        (lp.degreeWeightedProjection s n ((1 + weightedUltrasphericalRemainder s k B a₀ a) x)))
      (Ring.invertibleIndexFilter (fun n ↦ liftedFiniteSection (lp.degreeWeightedProjection s n)
        (weightedUltrasphericalRemainder s k B a₀ a)) atTop) (𝓝 x) :=
  lp.tendsto_degreeWeighted_system_solution s _
    (isCompactOperator_weightedUltrasphericalRemainder s k B a₀ a) hT x

/-- The zeroth-order operator agrees with its polynomial term. -/
theorem weightedUltrasphericalZeroTerm_coefficient (s k : ℕ) (a₀ p : ℝ[X])
    (v : lp.DegreeWeightedL2 s)
    (hv : weightedUltrasphericalPreconditioner s k v = chebyshevBasis.degreeWeightedCoefficient s p) :
    weightedUltrasphericalZeroTerm s k a₀ v =
      (ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s (a₀ * p) := by
  simp only [weightedUltrasphericalZeroTerm, comp_apply, hv,
    weightedChebyshevPolynomialMultiplier_coefficient, weightedChebyshevConversion_coefficient,
    weightedPositiveRaise_coefficient, zero_add]

/-- Each positive lower-order operator agrees with its polynomial term. -/
theorem weightedUltrasphericalPositiveTerm_coefficient (s k : ℕ) (j : Fin k) (a p : ℝ[X])
    (v : lp.DegreeWeightedL2 s)
    (hv : weightedUltrasphericalPreconditioner s k v = chebyshevBasis.degreeWeightedCoefficient s p) :
    weightedUltrasphericalPositiveTerm s k j a v =
      (ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s (a * ((derivative ^ (j.val + 1)) p)) := by
  simp only [weightedUltrasphericalPositiveTerm, comp_apply,
    weightedPreconditionedDerivative_coefficient s k j v p hv,
    weightedPositivePolynomialMultiplier_coefficient, weightedPositiveRaise_coefficient,
    Nat.add_sub_of_le (Nat.le_of_lt j.isLt)]


/-- The assembled interior operator agrees with the entire polynomial differential expression. -/
theorem weightedUltraspherical_polynomial_equation (s k : ℕ) (a₀ p : ℝ[X])
    (a : Fin k → ℝ[X]) (v : lp.DegreeWeightedL2 s)
    (hv : weightedUltrasphericalPreconditioner s k v = chebyshevBasis.degreeWeightedCoefficient s p) :
    ((lp.degreeWeightedShiftLeft s)^(k + 1)) v + weightedUltrasphericalLowerTerms s k a₀ a v =
      (ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s
        ((derivative^(k + 1)) p + a₀ * p + ∑ j : Fin k, a j * ((derivative^(j.val + 1)) p)) := by
  have htop := weightedPreconditionedDerivative_coefficient s k k v p hv
  rw [weightedPreconditionedDerivative_top] at htop
  rw [weightedUltrasphericalLowerTerms, add_apply, sum_apply, htop,
    weightedUltrasphericalZeroTerm_coefficient s k a₀ p v hv]
  simp only [weightedUltrasphericalPositiveTerm_coefficient s k _ _ p v hv]
  rw [Module.Basis.degreeWeightedCoefficient_add, Module.Basis.degreeWeightedCoefficient_add]
  have hsum (t : Finset (Fin k)) :
      (ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s
        (∑ j ∈ t, a j * ((derivative^(j.val + 1)) p)) =
      ∑ j ∈ t, (ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s
        (a j * ((derivative^(j.val + 1)) p)) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      apply Subtype.ext
      funext i
      change (((ultrasphericalBasis (k + 1)).repr 0 i : ℝ) : ℂ) = 0
      simp
    | @insert j t hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        Module.Basis.degreeWeightedCoefficient_add, ih]
  rw [hsum]
  abel

/-- The first k+1 rows impose the chosen bounded boundary conditions. -/
theorem weightedUltraspherical_boundary_rows (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (v : lp.DegreeWeightedL2 s) (i : Fin (k + 1)) :
    ((1 + weightedUltrasphericalRemainder s k B a₀ a) v).1 i = (B v).1 i := by
  rw [weightedUltrasphericalRemainder, lp.degreeWeightedBorderedRemainder_rows,
    ite_eq_left i.isLt]

/-- Every interior row is the corresponding ultraspherical coordinate of the polynomial residual. -/
theorem weightedUltraspherical_interior_polynomial_rows (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ p : ℝ[X]) (a : Fin k → ℝ[X])
    (v : lp.DegreeWeightedL2 s)
    (hv : weightedUltrasphericalPreconditioner s k v = chebyshevBasis.degreeWeightedCoefficient s p)
    (i : ℕ) :
    ((1 + weightedUltrasphericalRemainder s k B a₀ a) v).1 (i + k + 1) =
      ((ultrasphericalBasis (k + 1)).repr
        ((derivative^(k + 1)) p + a₀ * p + ∑ j : Fin k, a j * ((derivative^(j.val + 1)) p)) i : ℂ) := by
  have h := congrArg (fun x : lp.DegreeWeightedL2 s ↦ x.1 i)
    (weightedUltraspherical_polynomial_equation s k a₀ p a v hv)
  change (((lp.degreeWeightedShiftLeft s)^(k + 1)) v).1 i +
    (weightedUltrasphericalLowerTerms s k a₀ a v).1 i = _ at h
  rw [lp.degreeWeightedShiftLeft_pow_apply] at h
  rw [weightedUltrasphericalRemainder, lp.degreeWeightedBorderedRemainder_rows,
    ite_eq_right (by omega), show i + k + 1 - (k + 1) = i by omega]
  simpa only [Nat.add_assoc, Module.Basis.degreeWeightedCoefficient] using h

end Polynomial.Chebyshev
