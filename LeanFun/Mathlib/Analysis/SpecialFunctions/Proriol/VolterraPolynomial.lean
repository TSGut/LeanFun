/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.MarginalOperator

/-! # Volterra operators from polynomial triangle operations

Extension in the inner variable, multiplication by a consistently reflected
kernel, marginal integration, and reflection of the output assemble the exact
Volterra integral. Reference: Gutleb–Olver, arXiv:1906.03907, Sections 3.1–3.2.
This file makes no infinite-dimensional boundedness or solver claim.
-/

@[expose] public noncomputable section
namespace MvPolynomial
open Polynomial

/-- Extension of a univariate polynomial to the inner triangle coordinate. -/
def triangleExtendY : ℝ[X] →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  Polynomial.aeval (X 1)

/-- Inner extension evaluates as `u(y)` at every point. -/
theorem eval_triangleExtendY (u : ℝ[X]) (x y : ℝ) :
    eval (![x,y] : Fin 2 → ℝ) (triangleExtendY u) = u.eval y := by
  change eval (![x,y] : Fin 2 → ℝ) (u.eval₂ C (X 1)) = _
  simp [eval_eval₂_C_X]

/-- Exact polynomial Volterra assembly: reflect the kernel, extend the input,
multiply, integrate on the simplex, then reflect the output coordinate. -/
def volterraPolynomial (K : MvPolynomial (Fin 2) ℝ) : ℝ[X] →ₗ[ℝ] (ℝ → ℝ) where
  toFun u x := triangleMarginal (triangleReflect K * triangleExtendY u) (1-x)
  map_add' u v := by
    funext x
    simp only [map_add, mul_add, Pi.add_apply]
  map_smul' c u := by
    funext x
    simp only [map_smul, mul_smul_comm, Pi.smul_apply, RingHom.id_apply]

/-- The assembled operator is exactly the Volterra integral, including `x = 0`.
For negative `x`, the usual oriented interval-integral convention applies. -/
theorem volterraPolynomial_apply (K : MvPolynomial (Fin 2) ℝ) (u : ℝ[X]) (x : ℝ) :
    volterraPolynomial K u x =
      ∫ y in (0 : ℝ)..x, eval (![x,y] : Fin 2 → ℝ) K * u.eval y := by
  change (∫ y in (0 : ℝ)..(1-(1-x)),
    eval (![1-x,y] : Fin 2 → ℝ) (triangleReflect K * triangleExtendY u)) = _
  simp only [map_mul, eval_triangleReflect, eval_triangleExtendY, sub_sub_cancel]

/-- Kernel assembly is additive, without any analytic side conditions for
polynomial kernels. -/
theorem volterraPolynomial_add (K L : MvPolynomial (Fin 2) ℝ) :
    volterraPolynomial (K+L) = volterraPolynomial K + volterraPolynomial L := by
  ext u x
  simp [volterraPolynomial, add_mul]

/-- Scalar multiples of kernels give scalar multiples of Volterra operators. -/
theorem volterraPolynomial_smul (c : ℝ) (K : MvPolynomial (Fin 2) ℝ) :
    volterraPolynomial (c • K) = c • volterraPolynomial K := by
  ext u x
  simp [volterraPolynomial]

end MvPolynomial
