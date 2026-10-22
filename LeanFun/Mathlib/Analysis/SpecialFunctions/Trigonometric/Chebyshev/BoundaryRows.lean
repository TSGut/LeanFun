/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Operators
public import LeanFun.Mathlib.RingTheory.Polynomial.Chebyshev.Calculus
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-! # Boundary rows for finite Chebyshev expansions
Endpoint values and first derivatives use the full constant coefficient.
Reference: Olver--Townsend (2013), §2, boundary bordering.
-/

@[expose] public section
namespace Polynomial

/-- A scalar linear functional acts on finite Chebyshev coefficients by its row
of values on basis polynomials (Olver--Townsend 2013, §2). -/
theorem chebyshevBasis_functional_apply (L : ℝ[X] →ₗ[ℝ] ℝ) (v : ℕ →₀ ℝ) :
    L (chebyshevBasis.repr.symm v) =
      ∑ j ∈ v.support, v j * L (chebyshevBasis j) := by
  classical
  conv_lhs => rw [← v.sum_single]
  simp [Finsupp.sum, map_smul, smul_eq_mul]

/-- Evaluation at the right endpoint is the row of ones. -/
theorem chebyshevBasis_eval_one (v : ℕ →₀ ℝ) :
    (chebyshevBasis.repr.symm v).eval 1 = ∑ j ∈ v.support, v j := by
  simpa [chebyshevBasis_apply, Chebyshev.T_eval_one] using
    chebyshevBasis_functional_apply (leval (1 : ℝ)) v

/-- Evaluation at the left endpoint is the alternating row. -/
theorem chebyshevBasis_eval_neg_one (v : ℕ →₀ ℝ) :
    (chebyshevBasis.repr.symm v).eval (-1) =
      ∑ j ∈ v.support, v j * (-1 : ℝ) ^ j := by
  simpa [chebyshevBasis_apply, Chebyshev.T_eval_neg_one] using
    chebyshevBasis_functional_apply (leval (-1 : ℝ)) v

/-- The right endpoint derivative row is the sequence of squared degrees. -/
theorem chebyshevBasis_derivative_eval_one (v : ℕ →₀ ℝ) :
    (derivative (chebyshevBasis.repr.symm v)).eval 1 =
      ∑ j ∈ v.support, v j * (j : ℝ) ^ 2 := by
  simpa [chebyshevBasis_apply, Chebyshev.derivative_T_eval_one] using
    chebyshevBasis_functional_apply ((leval (1 : ℝ)).comp derivative) v

/-- The left endpoint derivative row includes the zero constant entry. -/
theorem chebyshevBasis_derivative_eval_neg_one (v : ℕ →₀ ℝ) :
    (derivative (chebyshevBasis.repr.symm v)).eval (-1) =
      ∑ j ∈ v.support, v j * ((-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ 2) := by
  have h (j : ℕ) : (derivative (chebyshevBasis j)).eval (-1) =
      (-1 : ℝ) ^ (j + 1) * (j : ℝ) ^ 2 := by
    cases j with
    | zero => simp [chebyshevBasis_apply, Chebyshev.T_zero]
    | succ j =>
      rw [chebyshevBasis_apply, Chebyshev.derivative_T_succ_eval_neg_one]
      simp [pow_succ, Nat.cast_add, Nat.cast_one]
  simpa only [LinearMap.comp_apply, leval_apply, h] using
    chebyshevBasis_functional_apply ((leval (-1 : ℝ)).comp derivative) v

end Polynomial
