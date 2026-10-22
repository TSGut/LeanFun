/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2Multiplication

/-! # Numerical norm bounds for raw Jacobi factors

Conservative bounds from the shift and reciprocal-diagonal decomposition.
Reference: Gutleb's thesis, §2.7.
-/
@[expose] public noncomputable section
namespace Polynomial
local notation "E" => lp (fun _ : ℕ ↦ ℝ) 2
local notation "F" => LinearIsometry.toContinuousLinearMap (lp.forwardShiftL2 (𝕜 := ℝ))
local notation "B" => (lp.backwardShiftL2 (𝕜 := ℝ))

private theorem forward_bound : ‖F‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _
private theorem backward_bound : ‖B‖ ≤ 1 := by
  simpa only [lp.backwardShiftL2,LinearIsometryEquiv.norm_map] using forward_bound
private theorem diagonal_bound (a b : ℕ) (hb : 0 < b) :
    ‖lp.reciprocalAffineDiagonal a b hb‖ ≤ 1 :=
  lp.norm_coefficientDiagonal_le _ _ _
private theorem comp_bound {A C : E →L[ℝ] E} (hA : ‖A‖ ≤ 1) (hC : ‖C‖ ≤ 1) :
    ‖A.comp C‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by nlinarith [norm_nonneg A,norm_nonneg C])

/-- The common constant tridiagonal part has norm at most one. -/
theorem norm_shiftedJacobiToeplitzPart_le : ‖shiftedJacobiToeplitzPart‖ ≤ 1 := by
  have h := norm_add_le ((1/2 : ℝ) • (1 : E →L[ℝ] E)) ((1/4 : ℝ) • (F+B))
  have hsum := (norm_add_le F B).trans (add_le_add forward_bound backward_bound)
  have hid : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  simp only [norm_smul,Real.norm_eq_abs] at h
  norm_num only at h
  unfold shiftedJacobiToeplitzPart
  nlinarith

/-- A conservative numerical bound for raw shifted Jacobi multiplication. -/
theorem norm_shiftedJacobiOneZeroL2_le : ‖shiftedJacobiOneZeroL2‖ ≤ 2 := by
  have h1 := comp_bound forward_bound (diagonal_bound 2 3 (by norm_num))
  have h2 := comp_bound (diagonal_bound 2 1 (by norm_num)) (diagonal_bound 2 3 (by norm_num))
  have h3 := comp_bound backward_bound (diagonal_bound 2 1 (by norm_num))
  have hc : ‖shiftedJacobiOneZeroCorrection‖ ≤ 1 := by
    unfold shiftedJacobiOneZeroCorrection
    apply (norm_sub_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    simp only [norm_smul,Real.norm_eq_abs]
    norm_num only
    nlinarith
  exact (norm_add_le _ _).trans (by linarith [norm_shiftedJacobiToeplitzPart_le])

/-- A conservative numerical bound for the reflected preconditioned factor. -/
theorem norm_reflectedJacobiOneZeroL2_le : ‖reflectedJacobiOneZeroL2‖ ≤ 3 := by
  have h1 := comp_bound forward_bound (diagonal_bound 1 1 (by norm_num))
  have h2 := comp_bound forward_bound (diagonal_bound 2 3 (by norm_num))
  have h3 := comp_bound (diagonal_bound 2 1 (by norm_num)) (diagonal_bound 2 3 (by norm_num))
  have h4 := comp_bound backward_bound (diagonal_bound 1 1 (by norm_num))
  have h5 := comp_bound backward_bound (diagonal_bound 2 1 (by norm_num))
  have hc : ‖reflectedJacobiOneZeroCorrection‖ ≤ 2 := by
    unfold reflectedJacobiOneZeroCorrection
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    apply (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans
    apply (add_le_add (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl) le_rfl).trans
    simp only [norm_smul,Real.norm_eq_abs]
    norm_num only
    nlinarith
  exact (norm_add_le _ _).trans (by linarith [norm_shiftedJacobiToeplitzPart_le])
end Polynomial
