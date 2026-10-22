/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Operators
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.MultiplicationOperator
public import LeanFun.Mathlib.Algebra.Polynomial.DifferentialOperator

/-! # First-order ultraspherical differential operators
Assemble variable polynomial coefficients with Chebyshev input and `C^(1)`
output. Boundary constraints and invertibility are separate from this residual
operator. Reference: Olver--Townsend (2013), Section 2.
-/

public section
namespace Polynomial
open Module

/-- The first-order ultraspherical residual has explicit lower and upper
bandwidths, including the conversion term and full-constant column. -/
theorem chebyshev_firstOrder_isBanded (a : ℕ → ℝ[X]) :
    ((gegenbauerBasis (by norm_num : -(1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) ≠ 0)).toMatrix
      (fun j ↦ differentialOperator a 1 (chebyshevBasis j))).IsBanded
        (max (a 0).natDegree (a 1).natDegree)
        (max ((a 0).natDegree + 2) ((a 1).natDegree + 1)) := by
  let b := chebyshevBasis
  let c := gegenbauerBasis (by norm_num : -(1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) ≠ 0)
  have hm (p : ℝ[X]) : (c.toMatrix (fun j ↦ p * c j)).IsBanded p.natDegree p.natDegree :=
    gegenbauerBasis_polynomial_mul_isBanded _ _ p
  have hc : (c.toMatrix (fun j ↦ (LinearMap.id : Module.End ℝ ℝ[X]) (b j))).IsBanded 0 2 :=
    chebyshevBasis_conversion_isBanded
  have hd : (c.toMatrix (fun j ↦ derivative (b j))).IsBanded 0 1 := by
    simpa only [Nat.cast_zero, zero_add, Nat.zero_add, Function.iterate_one] using
      chebyshevBasis_iterate_derivative_isBanded 0
  have h₀ := b.toMatrix_comp_isBanded c c LinearMap.id (LinearMap.mulLeft ℝ (a 0)) hc (hm _)
  have h₁ := b.toMatrix_comp_isBanded c c derivative (LinearMap.mulLeft ℝ (a 1)) hd (hm _)
  have h₀' := h₀.mono (show 0 + (a 0).natDegree ≤ max (a 0).natDegree (a 1).natDegree by omega)
    (show 2 + (a 0).natDegree ≤ max ((a 0).natDegree + 2) ((a 1).natDegree + 1) by omega)
  have h₁' := h₁.mono (show 0 + (a 1).natDegree ≤ max (a 0).natDegree (a 1).natDegree by omega)
    (show 1 + (a 1).natDegree ≤ max ((a 0).natDegree + 2) ((a 1).natDegree + 1) by omega)
  intro i j hij
  change c.repr (differentialOperator a 1 (b j)) i = 0
  rw [differentialOperator_one_apply, map_add, Finsupp.add_apply]
  have hz₀ : c.repr (a 0 * b j) i = 0 := h₀' i j hij
  have hz₁ : c.repr (a 1 * derivative (b j)) i = 0 := h₁' i j hij
  rw [hz₀, hz₁, add_zero]

end Polynomial
