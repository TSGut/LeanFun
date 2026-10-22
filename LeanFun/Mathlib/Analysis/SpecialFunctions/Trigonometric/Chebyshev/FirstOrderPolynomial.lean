/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.BoundedCoefficientOperators
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.FirstOrderRepresentation

/-! # Polynomial-coefficient first-order ultraspherical solves
The lower-order term in u' + p(x)u is bounded polynomial multiplication followed
by conversion from T to U. Preconditioning gives I plus a compact operator.
Reference: Olver--Townsend (2013), Sections 2 and 4.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open ContinuousLinearMap Filter Set
open scoped Topology

/-- The lower-order term of u' + p(x)u, in the derivative's U coordinates. -/
noncomputable def firstOrderPolynomialTerm (p : ℝ[X]) :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  boundedConversion.comp (boundedPolynomialMultiplier p)

/-- This bounded operator extends exactly the existing polynomial basis map. -/
theorem firstOrderPolynomialTerm_coefficientLp (p q : ℝ[X]) :
    firstOrderPolynomialTerm p (chebyshevBasis.coefficientLp q) =
      (ultrasphericalBasis 1).coefficientLp (p * q) := by
  change boundedConversion (boundedPolynomialMultiplier p (chebyshevBasis.coefficientLp q)) = _
  rw [boundedPolynomialMultiplier_coefficientLp, boundedConversion_coefficientLp]

/-- Every polynomial lower-order coefficient gives a compact remainder. -/
theorem isCompactOperator_firstOrderPolynomial (p : ℝ[X]) :
    IsCompactOperator (firstOrderCompactRemainder (firstOrderPolynomialTerm p)) :=
  isCompactOperator_firstOrderCompactRemainder _

/-- Invertibility of the infinite polynomial operator implies unique large finite
sections. Invertibility is an explicit hypothesis, not inferred from compactness. -/
theorem eventually_existsUnique_firstOrderPolynomial_system (p : ℝ[X])
    (hp : IsUnit (1 + firstOrderCompactRemainder (firstOrderPolynomialTerm p))) :
    ∀ᶠ n in atTop, ∀ f : lp (fun _ : ℕ ↦ ℂ) 2, ∃! x : lp (fun _ : ℕ ↦ ℂ) 2,
      (∀ i, n ≤ i → x i = 0) ∧
        (∀ i < n, ((1 + firstOrderCompactRemainder (firstOrderPolynomialTerm p)) x) i = f i) :=
  eventually_existsUnique_firstOrder_system _ hp

set_option maxHeartbeats 800000 in
/-- Actual finite polynomial-coefficient solves converge uniformly on the typed interval. -/
theorem tendstoUniformlyOn_firstOrderPolynomial_solution (p : ℝ[X])
    (hp : IsUnit (1 + firstOrderCompactRemainder (firstOrderPolynomialTerm p)))
    (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    TendstoUniformly
      (fun n : Ring.InvertibleIndex (fun n ↦ liftedFiniteSection (lp.coefficientProjection n)
          (firstOrderCompactRemainder (firstOrderPolynomialTerm p))) ↦
        fun t : Icc (-1 : ℝ) 1 ↦
        let v := Ring.inverseAt (fun n ↦ liftedFiniteSection (lp.coefficientProjection n)
          (firstOrderCompactRemainder (firstOrderPolynomialTerm p))) n
          (lp.coefficientProjection n.val
            ((1 + firstOrderCompactRemainder (firstOrderPolynomialTerm p)) x))
        complexChebyshevSeries (firstOrderPreconditioner v) (.ofFirstOrder v t))
      (fun t ↦ complexChebyshevSeries (firstOrderPreconditioner x) (.ofFirstOrder x t))
      (Ring.invertibleIndexFilter (fun n ↦ liftedFiniteSection (lp.coefficientProjection n)
        (firstOrderCompactRemainder (firstOrderPolynomialTerm p))) atTop) := by
  have h := tendsto_liftedFiniteSection_solution
    (lp.coefficientProjection (𝕜 := ℂ)) (lp.norm_coefficientProjection_le (𝕜 := ℂ))
    (lp.tendsto_coefficientProjection (𝕜 := ℂ))
    (firstOrderCompactRemainder (firstOrderPolynomialTerm p))
    (isCompactOperator_firstOrderPolynomial p) hp x
  exact tendstoUniformlyOn_firstOrder_reconstruction h

end Polynomial.Chebyshev
