/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Lp.CoefficientOperators
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Compact reciprocal diagonals

Reciprocal affine sequences supply the compact corrections of Jacobi matrices.
Reference: Gutleb, Sparse spectral methods for integral equations and equilibrium
measures, §2.7.
-/

@[expose] public noncomputable section
namespace lp
open Filter
open scoped Topology

/-- A reciprocal affine diagonal with positive integral offset is bounded by one. -/
theorem norm_reciprocalAffine_le_one (a b n : ℕ) (hb : 0 < b) :
    ‖((a : ℝ)*n+b)⁻¹‖ ≤ 1 := by
  have h : (1 : ℝ) ≤ (a : ℝ)*n+b := by
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
  exact inv_le_one_of_one_le₀ h

/-- Reciprocal affine diagonals on real square-summable sequences. -/
def reciprocalAffineDiagonal (a b : ℕ) (hb : 0 < b) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  coefficientDiagonal (fun n ↦ ((a : ℝ)*n+b)⁻¹) zero_le_one
    (fun n ↦ norm_reciprocalAffine_le_one a b n hb)

/-- The diagonal entries are the prescribed reciprocal affine sequence. -/
@[simp] theorem reciprocalAffineDiagonal_apply (a b : ℕ) (hb : 0 < b)
    (u : lp (fun _ : ℕ ↦ ℝ) 2) (n : ℕ) :
    reciprocalAffineDiagonal a b hb u n = ((a : ℝ)*n+b)⁻¹*u n := rfl

/-- A positive slope makes the reciprocal diagonal compact. -/
theorem isCompactOperator_reciprocalAffineDiagonal (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    IsCompactOperator (reciprocalAffineDiagonal a b hb) := by
  apply isCompactOperator_coefficientDiagonal
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_atTop_add_const_right atTop (b : ℝ)
    (Filter.Tendsto.const_mul_atTop (show (0 : ℝ) < (a : ℝ) by exact_mod_cast ha)
      (tendsto_natCast_atTop_atTop (R := ℝ)))

end lp
