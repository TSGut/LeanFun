/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.CoefficientPreconditioner
public import LeanFun.Mathlib.Analysis.Normed.Lp.FiniteSection

/-! # First-order bordered ultraspherical finite sections
A bounded lower-order coefficient operator, followed by the compact diagonal
preconditioner, gives a compact perturbation of the normalized derivative.
The pure derivative boundary-value problem has an explicit inverse.
Reference: Olver--Townsend (2013), Section 4.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open ContinuousLinearMap Filter
open scoped Topology

/-- Rank-one correction imposing evaluation at -1 after preconditioning. -/
noncomputable def firstOrderBoundaryCorrection :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  (firstOrderBoundary - lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 2 0).smulRight
    (lp.single (E := fun _ : ℕ ↦ ℂ) 2 0 (1 : ℂ))

/-- The boundary correction is compact. -/
theorem isCompactOperator_firstOrderBoundaryCorrection :
    IsCompactOperator firstOrderBoundaryCorrection := by
  change IsCompactOperator (((ContinuousLinearMap.id ℂ ℂ).smulRight
    (lp.single (E := fun _ : ℕ ↦ ℂ) 2 0 (1 : ℂ))).comp
      (firstOrderBoundary - lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 2 0))
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (firstOrderBoundary - lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 2 0)).clm_comp
      ((ContinuousLinearMap.id ℂ ℂ).smulRight
        (lp.single (E := fun _ : ℕ ↦ ℂ) 2 0 (1 : ℂ)))

/-- The correction only changes the first row. -/
@[simp] theorem firstOrderBoundaryCorrection_apply
    (x : lp (fun _ : ℕ ↦ ℂ) 2) (i : ℕ) :
    firstOrderBoundaryCorrection x i = if i = 0 then firstOrderBoundary x - x 0 else 0 := by
  change (firstOrderBoundary x - x 0) * (lp.single (E := fun _ : ℕ ↦ ℂ) 2 0 (1 : ℂ) i) = _
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs <;> simp_all

/-- The pure-derivative boundary correction squares to zero. -/
theorem firstOrderBoundaryCorrection_sq : firstOrderBoundaryCorrection ^ 2 = 0 := by
  ext x i
  have he : firstOrderBoundaryCorrection (lp.single (E := fun _ : ℕ ↦ ℂ) 2 0 (1 : ℂ)) = 0 := by
    ext j
    simp [firstOrderBoundary_single_zero]
  rw [pow_two, mul_apply_eq_comp]
  change firstOrderBoundaryCorrection (firstOrderBoundaryCorrection x) i = 0
  change firstOrderBoundaryCorrection
    ((firstOrderBoundary x - x 0) • lp.single (E := fun _ : ℕ ↦ ℂ) 2 0 (1 : ℂ)) i = 0
  rw [map_smul, he, smul_zero]
  rfl

/-- The normalized bordered derivative is invertible, with inverse I minus its
rank-one correction. No solvability assumption is needed in this example. -/
theorem isUnit_firstOrderDerivative : IsUnit (1 + firstOrderBoundaryCorrection) := by
  have h : firstOrderBoundaryCorrection * firstOrderBoundaryCorrection = 0 := by
    simpa only [pow_two] using firstOrderBoundaryCorrection_sq
  refine ⟨⟨1 + firstOrderBoundaryCorrection, 1 - firstOrderBoundaryCorrection, ?_, ?_⟩, rfl⟩
  · calc
      _ = 1 - firstOrderBoundaryCorrection * firstOrderBoundaryCorrection := by simp only [mul_sub, add_mul, one_mul, mul_one]; abel
      _ = 1 := by rw [h, sub_zero]
  · calc
      _ = 1 - firstOrderBoundaryCorrection * firstOrderBoundaryCorrection := by simp only [sub_mul, mul_add, one_mul, mul_one]; abel
      _ = 1 := by rw [h, sub_zero]

/-- Compact remainder for a normalized first-order equation. A maps Chebyshev
coefficients of the lower-order term to the derivative's U-basis coefficients. -/
noncomputable def firstOrderCompactRemainder
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2) :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  firstOrderBoundaryCorrection + lp.coefficientShiftRight.comp (A.comp firstOrderPreconditioner)

/-- Lower-order bounded coefficient terms become compact after preconditioning. -/
theorem isCompactOperator_firstOrderCompactRemainder
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2) :
    IsCompactOperator (firstOrderCompactRemainder A) :=
  isCompactOperator_firstOrderBoundaryCorrection.add
    ((isCompactOperator_firstOrderPreconditioner.clm_comp A).clm_comp lp.coefficientShiftRight)

/-- Row zero imposes the endpoint condition. -/
theorem firstOrder_bordered_row_zero
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    ((1 + firstOrderCompactRemainder A) x) 0 = firstOrderBoundary x := by
  simp [firstOrderCompactRemainder, add_apply, one_apply_eq_self]

/-- Remaining rows are the preconditioned derivative plus the lower-order term. -/
theorem firstOrder_bordered_row_succ
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (x : lp (fun _ : ℕ ↦ ℂ) 2) (i : ℕ) :
    ((1 + firstOrderCompactRemainder A) x) (i + 1) =
      x (i + 1) + A (firstOrderPreconditioner x) i := by
  simp [firstOrderCompactRemainder, add_apply, one_apply_eq_self]

/-- Unique finite systems for the normalized first-order operator, conditional
on invertibility of the infinite bordered operator. -/
theorem eventually_existsUnique_firstOrder_system
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (hA : IsUnit (1 + firstOrderCompactRemainder A)) :
    ∀ᶠ n in atTop, ∀ f : lp (fun _ : ℕ ↦ ℂ) 2, ∃! x : lp (fun _ : ℕ ↦ ℂ) 2,
      (∀ i, n ≤ i → x i = 0) ∧
        (∀ i < n, ((1 + firstOrderCompactRemainder A) x) i = f i) :=
  lp.eventually_existsUnique_coefficient_system _ (isCompactOperator_firstOrderCompactRemainder A) hA

/-- First-order finite sections converge in preconditioned coefficient norm. -/
theorem tendsto_firstOrder_system_solution
    (A : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (hA : IsUnit (1 + firstOrderCompactRemainder A)) (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    Tendsto (fun n : Ring.InvertibleIndex
        (fun n ↦ liftedFiniteSection (lp.coefficientProjection n) (firstOrderCompactRemainder A)) ↦
      Ring.inverseAt (fun n ↦ liftedFiniteSection (lp.coefficientProjection n) (firstOrderCompactRemainder A)) n
        (lp.coefficientProjection n ((1 + (firstOrderCompactRemainder A)) x)))
      (Ring.invertibleIndexFilter
        (fun n ↦ liftedFiniteSection (lp.coefficientProjection n) (firstOrderCompactRemainder A)) atTop) (𝓝 x) :=
  lp.tendsto_coefficient_system_solution _ (isCompactOperator_firstOrderCompactRemainder A) hA x

/-- The pure derivative boundary-value problem has convergent finite solves
without an invertibility hypothesis. -/
theorem tendsto_firstOrder_derivative_solution (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    Tendsto (fun n : Ring.InvertibleIndex
        (fun n ↦ liftedFiniteSection (lp.coefficientProjection n) firstOrderBoundaryCorrection) ↦
      Ring.inverseAt (fun n ↦ liftedFiniteSection (lp.coefficientProjection n) firstOrderBoundaryCorrection) n
        (lp.coefficientProjection n ((1 + firstOrderBoundaryCorrection) x)))
      (Ring.invertibleIndexFilter
        (fun n ↦ liftedFiniteSection (lp.coefficientProjection n) firstOrderBoundaryCorrection) atTop) (𝓝 x) :=
  lp.tendsto_coefficient_system_solution _ isCompactOperator_firstOrderBoundaryCorrection
    isUnit_firstOrderDerivative x

end Polynomial.Chebyshev
