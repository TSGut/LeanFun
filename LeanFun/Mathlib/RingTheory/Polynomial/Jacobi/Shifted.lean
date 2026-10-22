/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Ring

/-! # Jacobi polynomials on the unit interval
The affine composition P_n(2x-1) is used by the triangle construction.
Reference: DLMF 18.37.7.
-/

@[expose] public section
namespace Polynomial

/-- The standard Jacobi polynomial evaluated at the affine coordinate 2x-1. -/
noncomputable def shiftedJacobi (α β : ℝ) (n : ℕ) : ℝ[X] :=
  (jacobi α β n).comp (C 2 * X - 1)

@[simp] theorem eval_shiftedJacobi (α β : ℝ) (n : ℕ) (x : ℝ) :
    (shiftedJacobi α β n).eval x = (jacobi α β n).eval (2 * x - 1) := by
  simp [shiftedJacobi]

/-- The affine shift does not increase polynomial degree. -/
theorem natDegree_shiftedJacobi_le (α β : ℝ) (n : ℕ) :
    (shiftedJacobi α β n).natDegree ≤ n := by
  unfold shiftedJacobi
  apply natDegree_comp_le.trans
  have hd : (C (2 : ℝ) * X - 1).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_mul_le).trans (by simp)) (by simp))
  exact (Nat.mul_le_mul (natDegree_jacobi_le α β n) hd).trans (by simp)

/-- The inverse affine coordinate recovers the original Jacobi value. -/
theorem eval_shiftedJacobi_half_add_one (α β : ℝ) (n : ℕ) (t : ℝ) :
    (shiftedJacobi α β n).eval ((t + 1) / 2) = (jacobi α β n).eval t := by
  rw [eval_shiftedJacobi]
  congr 1
  ring

end Polynomial
