/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Operators
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ModificationOperators

/-! # Polynomial multiplication in Gegenbauer coordinates
Reference: Olver--Townsend (2013), Sections 2--3.
-/

public section
namespace Polynomial

/-- A polynomial multiplier of degree `d` has bandwidths `(d,d)` in the
Gegenbauer basis throughout its nondegenerate orthogonality range. -/
theorem gegenbauerBasis_polynomial_mul_isBanded {lam : ℝ}
    (hlam : -(1 / 2) < lam) (hzero : lam ≠ 0) (p : ℝ[X]) :
    ((gegenbauerBasis hlam hzero).toMatrix
      (fun j ↦ p * gegenbauerBasis hlam hzero j)).IsBanded p.natDegree p.natDegree := by
  simpa only [gegenbauerBasis, Sequence.basis_eq_self] using
    (isOrthogonal_gegenbauerSequence hlam hzero).polynomial_mul_isBanded
      (hasFiniteMoments_gegenbauerMeasure hlam)
      (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)
      (fun n ↦ isUnit_iff_ne_zero.mpr
        (leadingCoeff_ne_zero.mpr ((gegenbauerSequence hlam hzero).ne_zero n))) p

end Polynomial
