/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraPolynomial
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Lowering
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Volterra extension and marginal on shifted Jacobi modes

The zero-based diagonal of the extension/marginal composition is
`(-1)^n/(n+1)`, before multiplying by `1-x`. Reference: Gutleb–Olver,
arXiv:1906.03907, Section 3.1; Gutleb's thesis, Section 2.3.
-/

public section
open MeasureTheory
namespace Polynomial

/-- The endpoint-vanishing primitive underlying the Volterra Jacobi diagonal. -/
theorem hasDerivAt_mul_shiftedJacobi_zero_one (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t ↦ t * (shiftedJacobi 0 1 n).eval t)
      (((n : ℝ)+1) * (shiftedJacobi 1 0 n).eval x) x := by
  have ha : HasDerivAt (fun t : ℝ ↦ 2*t-1) 2 x := by
    convert ((hasDerivAt_id x).const_mul 2).sub_const 1 using 1 <;> simp
  have hd := (hasDerivAt_id x).mul (((jacobi (0 : ℝ) 1 n).hasDerivAt (2*x-1)).comp x ha)
  have hi := congrArg (fun p : ℝ[X] ↦ p.eval (2*x-1)) (jacobi_lower_beta 0 1 n)
  norm_num only [zero_add, sub_self, eval_add, eval_mul, eval_C, eval_X, eval_one] at hi
  convert hd using 1
  · ext t
    simp [eval_shiftedJacobi]
  · simp only [eval_shiftedJacobi, Function.comp_apply, id_eq]
    linear_combination -hi

/-- Exact integration of a shifted `(1,0)` mode, including degree zero. -/
theorem integral_shiftedJacobi_one_zero (n : ℕ) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, (shiftedJacobi 1 0 n).eval t =
      x * (shiftedJacobi 0 1 n).eval x / ((n : ℝ)+1) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_mul_shiftedJacobi_zero_one n t)
    (((continuous_const.mul (shiftedJacobi 1 0 n).continuous)).intervalIntegrable 0 x)
  rw [intervalIntegral.integral_const_mul] at h
  simp only [zero_mul, sub_zero] at h
  apply (eq_div_iff (by positivity : (n : ℝ)+1 ≠ 0)).2
  simpa only [mul_comm] using h

end Polynomial
namespace MvPolynomial
open Polynomial

/-- Extension followed by marginal has diagonal `(-1)^n/(n+1)` when the
endpoint factor `1-x` is kept outside the coefficient operator. -/
theorem triangleMarginal_extendY_shiftedJacobi (n : ℕ) (x : ℝ) :
    triangleMarginal (triangleExtendY (shiftedJacobi 1 0 n)) x =
      ((-1 : ℝ)^n / ((n : ℝ)+1)) *
        ((1-x) * (shiftedJacobi 1 0 n).eval x) := by
  change (∫ y in (0 : ℝ)..(1-x), _) = _
  simp only [eval_triangleExtendY]
  rw [integral_shiftedJacobi_one_zero, eval_shiftedJacobi_one_sub]
  ring

/-- The constant-kernel Volterra operator maps a `(1,0)` mode to its anchored
primitive in the `(0,1)` basis. -/
theorem volterraPolynomial_one_shiftedJacobi (n : ℕ) (x : ℝ) :
    volterraPolynomial 1 (shiftedJacobi 1 0 n) x =
      x * (shiftedJacobi 0 1 n).eval x / ((n : ℝ)+1) := by
  rw [volterraPolynomial_apply]
  simp only [map_one, one_mul]
  exact integral_shiftedJacobi_one_zero n x

end MvPolynomial
