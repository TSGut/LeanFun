/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.ModifiedConnection

/-!
# Two sparse Cartesian disk modifications

The densities x²y² and (1-x²-y²)(2-2x²-y²) have separated inner degrees two
and four. Their exact support bounds are six and nine positions per column.
The modification may vanish inside the disk; strict positivity of polynomial
pairings follows from nonzero polynomial densities, not pointwise strict positivity.
Reference: the Cartesian measure-modification framework of Dunkl–Xu and
Gutleb–Olver–Slevinsky.
-/

@[expose] public section
open MeasureTheory Set Polynomial
namespace Polynomial

/-- The inner factor of the product of the two disk boundary quadratics. -/
noncomputable def diskBoundaryProductFactor : ℝ[X] := (1-X^2)*(2-X^2)

/-- The boundary-product factor is nonnegative on the inner interval. -/
theorem diskBoundaryProductFactor_nonneg {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ diskBoundaryProductFactor.eval x := by
  have hs : x^2 ≤ 1 := by nlinarith [hx.1,hx.2]
  simp only [diskBoundaryProductFactor,eval_mul,eval_sub,eval_one,eval_pow,eval_X,eval_ofNat]
  exact mul_nonneg (by linarith) (by linarith)

/-- The inner factor is nonzero, even though it vanishes at the endpoints. -/
theorem diskBoundaryProductFactor_ne_zero : diskBoundaryProductFactor ≠ 0 := by
  intro h
  have := congrArg (fun p : ℝ[X] => p.eval 0) h
  norm_num [diskBoundaryProductFactor] at this

/-- Its inner degree is at most four. -/
theorem natDegree_diskBoundaryProductFactor_le : diskBoundaryProductFactor.natDegree ≤ 4 := by
  have h₁ : (1-X^2 : ℝ[X]).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (by simp)
  have h₂ : (2-X^2 : ℝ[X]).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (by simp)
  exact natDegree_mul_le.trans (by omega)

/-- The factor has even reflection parity. -/
theorem diskBoundaryProductFactor_even (x : ℝ) :
    diskBoundaryProductFactor.eval (-x) = diskBoundaryProductFactor.eval x := by
  simp [diskBoundaryProductFactor]

end Polynomial
namespace MvPolynomial

/-- The first separated modification is exactly x²y². -/
theorem cartesianDiskModification_X_sq :
    cartesianDiskModification (Polynomial.X^2) (Polynomial.X^2) 1 =
      (X 0)^2*(X 1)^2 := by
  norm_num [cartesianDiskModification,cartesianDiskPolynomial,diskLift,Finset.sum_range_succ]

/-- The second separated modification is the product of the two stated quadratics. -/
theorem cartesianDiskModification_boundaryProduct :
    cartesianDiskModification 1 diskBoundaryProductFactor 2 =
      (1-(X 0)^2-(X 1)^2)*(2-2*(X 0)^2-(X 1)^2) := by
  have he : diskBoundaryProductFactor = 2-3*Polynomial.X^2+Polynomial.X^4 := by
    unfold diskBoundaryProductFactor
    ring
  rw [he]
  norm_num [cartesianDiskModification,cartesianDiskPolynomial,diskLift,Finset.sum_range_succ,
    Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul]
  simp only [map_ofNat]
  ring

/-- The target orthonormal Cartesian system for the x²y² modification. -/
noncomputable def dunklXuXYSystem {β : ℝ} (hβ : -1 < β) :
    CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification (Polynomial.X^2) 1 ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure (Polynomial.X^2) ((jacobiMeasure β β).comap Subtype.val)) := by
  let := isNegInvariant_jacobiMeasure β
  exact modifiedCartesianDiskSystem
    (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith))
    (hasPositiveDefiniteIntegral_jacobiMeasure (by linarith) (by linarith))
    (hasFiniteMoments_jacobiMeasure hβ hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ)
    (ae_mem_Icc_jacobiMeasure _ _) (Polynomial.X^2) (Polynomial.X^2) 1
    (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ Polynomial.X_ne_zero)
    (Filter.Eventually.of_forall (by intro x; simpa using sq_nonneg x))
    (Filter.Eventually.of_forall (by intro x; simpa using sq_nonneg x)) (by intro x; simp)

/-- The target orthonormal system for the boundary-product modification. -/
noncomputable def dunklXuBoundaryProductSystem {β : ℝ} (hβ : -1 < β) :
    CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification 1 2 ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure diskBoundaryProductFactor ((jacobiMeasure β β).comap Subtype.val)) := by
  let := isNegInvariant_jacobiMeasure β
  have hg : ∀ᵐ z ∂jacobiMeasure β β, 0 ≤ diskBoundaryProductFactor.eval z := by
    filter_upwards [ae_mem_Icc_jacobiMeasure β β] with z hz
    exact diskBoundaryProductFactor_nonneg hz
  exact modifiedCartesianDiskSystem
    (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith))
    (hasPositiveDefiniteIntegral_jacobiMeasure (by linarith) (by linarith))
    (hasFiniteMoments_jacobiMeasure hβ hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ)
    (ae_mem_Icc_jacobiMeasure _ _) 1 diskBoundaryProductFactor 2 one_ne_zero
    diskBoundaryProductFactor_ne_zero (Filter.Eventually.of_forall (by intro x; simp)) hg
    diskBoundaryProductFactor_even

end MvPolynomial
