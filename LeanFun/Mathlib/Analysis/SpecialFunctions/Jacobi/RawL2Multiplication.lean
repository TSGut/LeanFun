/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Lp.ReciprocalDiagonal
public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.Laurent
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalMultiplication

/-! # Raw Jacobi multiplication and its reflected preconditioner

Bounded tridiagonal realizations of the shifted (1,0) Jacobi coefficients.
Their common Toeplitz part has symbol (2+z+z⁻¹)/4.
Reference: Gutleb's thesis, §2.7. The reflected conjugation is D⁻¹(I-J)D.
-/

@[expose] public noncomputable section
namespace Polynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2

/-- The constant tridiagonal part of raw shifted Jacobi multiplication. -/
def shiftedJacobiToeplitzPart : H →L[ℝ] H :=
  (1/2 : ℝ) • 1 + (1/4 : ℝ) •
    (lp.forwardShiftL2.toContinuousLinearMap+lp.backwardShiftL2)

/-- The compact correction of shifted Jacobi (1,0) multiplication. -/
def shiftedJacobiOneZeroCorrection : H →L[ℝ] H :=
  (1/4 : ℝ) • lp.forwardShiftL2.toContinuousLinearMap.comp
    (lp.reciprocalAffineDiagonal 2 3 (by norm_num)) -
  (1/2 : ℝ) • (lp.reciprocalAffineDiagonal 2 1 (by norm_num)).comp
    (lp.reciprocalAffineDiagonal 2 3 (by norm_num)) -
  (1/4 : ℝ) • lp.backwardShiftL2.comp (lp.reciprocalAffineDiagonal 2 1 (by norm_num))

/-- Raw shifted Jacobi (1,0) multiplication on ℓ². -/
def shiftedJacobiOneZeroL2 : H →L[ℝ] H :=
  shiftedJacobiToeplitzPart+shiftedJacobiOneZeroCorrection

/-- The correction is compact because its reciprocal diagonals tend to zero. -/
theorem isCompactOperator_shiftedJacobiOneZeroCorrection :
    IsCompactOperator shiftedJacobiOneZeroCorrection := by
  have h1 := lp.isCompactOperator_reciprocalAffineDiagonal 2 1 (by norm_num) (by norm_num)
  have h3 := lp.isCompactOperator_reciprocalAffineDiagonal 2 3 (by norm_num) (by norm_num)
  unfold shiftedJacobiOneZeroCorrection
  apply IsCompactOperator.sub
  · apply IsCompactOperator.sub
    · exact (h3.clm_comp lp.forwardShiftL2.toContinuousLinearMap).smul (1/4 : ℝ)
    · exact (h1.comp_clm (lp.reciprocalAffineDiagonal 2 3 (by norm_num))).smul (1/2 : ℝ)
  · exact (h1.clm_comp lp.backwardShiftL2).smul (1/4 : ℝ)

/-- The reflected, diagonally preconditioned correction. -/
def reflectedJacobiOneZeroCorrection : H →L[ℝ] H :=
  (1/2 : ℝ) • lp.forwardShiftL2.toContinuousLinearMap.comp
    (lp.reciprocalAffineDiagonal 1 1 (by norm_num)) -
  (1/4 : ℝ) • lp.forwardShiftL2.toContinuousLinearMap.comp
    (lp.reciprocalAffineDiagonal 2 3 (by norm_num)) +
  (1/2 : ℝ) • (lp.reciprocalAffineDiagonal 2 1 (by norm_num)).comp
    (lp.reciprocalAffineDiagonal 2 3 (by norm_num)) -
  (1/2 : ℝ) • lp.backwardShiftL2.comp (lp.reciprocalAffineDiagonal 1 1 (by norm_num)) +
  (1/4 : ℝ) • lp.backwardShiftL2.comp (lp.reciprocalAffineDiagonal 2 1 (by norm_num))

/-- Bounded realization of the reflected preconditioner D⁻¹(I-J)D. -/
def reflectedJacobiOneZeroL2 : H →L[ℝ] H :=
  shiftedJacobiToeplitzPart+reflectedJacobiOneZeroCorrection

/-- The reflected preconditioner has a compact correction to the same Toeplitz part. -/
theorem isCompactOperator_reflectedJacobiOneZeroCorrection :
    IsCompactOperator reflectedJacobiOneZeroCorrection := by
  have h1 := lp.isCompactOperator_reciprocalAffineDiagonal 2 1 (by norm_num) (by norm_num)
  have h3 := lp.isCompactOperator_reciprocalAffineDiagonal 2 3 (by norm_num) (by norm_num)
  have hn := lp.isCompactOperator_reciprocalAffineDiagonal 1 1 (by norm_num) (by norm_num)
  unfold reflectedJacobiOneZeroCorrection
  apply IsCompactOperator.add
  · apply IsCompactOperator.sub
    · apply IsCompactOperator.add
      · apply IsCompactOperator.sub
        · exact (hn.clm_comp lp.forwardShiftL2.toContinuousLinearMap).smul (1/2 : ℝ)
        · exact (h3.clm_comp lp.forwardShiftL2.toContinuousLinearMap).smul (1/4 : ℝ)
      · exact (h1.comp_clm (lp.reciprocalAffineDiagonal 2 3 (by norm_num))).smul (1/2 : ℝ)
    · exact (hn.clm_comp lp.backwardShiftL2).smul (1/2 : ℝ)
  · exact (h1.clm_comp lp.backwardShiftL2).smul (1/4 : ℝ)

/-- The initial row of raw shifted Jacobi multiplication. -/
theorem shiftedJacobiOneZeroL2_apply_zero (u : H) :
    shiftedJacobiOneZeroL2 u 0 =
      shiftedJacobiOneZeroDiag 0*u 0 + shiftedJacobiOneZeroLower 1*u 1 := by
  simp only [shiftedJacobiOneZeroL2, shiftedJacobiToeplitzPart,
    shiftedJacobiOneZeroCorrection, ContinuousLinearMap.comp_apply,
    add_apply, sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_add, lp.coeFn_sub,
    lp.coeFn_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    LinearIsometry.coe_toContinuousLinearMap, lp.forwardShiftL2_zero,
    lp.backwardShiftL2_apply, lp.reciprocalAffineDiagonal_apply,
    shiftedJacobiOneZeroDiag, shiftedJacobiOneZeroLower]
  norm_num
  ring

/-- Every remaining row has precisely the three Jacobi recurrence entries. -/
theorem shiftedJacobiOneZeroL2_apply_succ (u : H) (n : ℕ) :
    shiftedJacobiOneZeroL2 u (n+1) = shiftedJacobiOneZeroUpper n*u n +
      shiftedJacobiOneZeroDiag (n+1)*u (n+1) +
      shiftedJacobiOneZeroLower (n+2)*u (n+2) := by
  simp only [shiftedJacobiOneZeroL2, shiftedJacobiToeplitzPart,
    shiftedJacobiOneZeroCorrection, ContinuousLinearMap.comp_apply,
    add_apply, sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_add, lp.coeFn_sub,
    lp.coeFn_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    LinearIsometry.coe_toContinuousLinearMap, lp.forwardShiftL2_succ,
    lp.backwardShiftL2_apply, lp.reciprocalAffineDiagonal_apply,
    shiftedJacobiOneZeroUpper, shiftedJacobiOneZeroDiag, shiftedJacobiOneZeroLower,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  ring

end Polynomial
