/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalCoordinates
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
/-! # Norms of the raw shifted Jacobi (1,0) basis

The affine Jacobi measure has density 4(1-x) on [0,1]. Its standard, unnormalized
basis has squared norm 2/(n+1). Reference: DLMF Table 18.3.1.
-/

@[expose] public noncomputable section
open MeasureTheory Real
namespace Polynomial
/-- The raw shifted (1,0) Jacobi squared norm after affine transport. -/
theorem integral_sq_shiftedJacobi_one_zero (n : ℕ) :
    (∫ x, (shiftedJacobi 1 0 n).eval x ^ 2 ∂unitJacobiMeasure 1 0) =
      2 / ((n : ℝ) + 1) := by
  have he := integralInner_shiftedJacobi 1 0 n n
    (hi := (hasFiniteMoments_jacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _)
  simp only [integralInner, ← sq] at he
  rw [he]
  cases n with
  | zero =>
    rw [integral_sq_jacobi_zero (by norm_num) (by norm_num)]
    norm_num [GammaOn, GammaPoint.ofPos, Gamma_add_one, Gamma_one]
  | succ n =>
    rw [integral_sq_jacobi_succ (by norm_num) (by norm_num)]
    simp only [GammaOn, GammaPoint.ofPos]
    have hG : Gamma ((n : ℝ) + 1 + 2) ≠ 0 :=
      (Gamma_pos_of_pos (by positivity)).ne'
    have hF : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
    have hG2 : Gamma ((n : ℝ) + 0 + 2) = (n + 1).factorial := by
      rw [show (n : ℝ) + 0 + 2 = ((n+1 : ℕ) : ℝ) + 1 by push_cast; ring]
      exact Gamma_nat_eq_factorial (n+1)
    rw [hG2]
    norm_num only [add_zero, zero_add, Nat.cast_add, Nat.cast_one, Real.rpow_natCast]
    field_simp
    ring
end Polynomial
