/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.Normed.Lp.DegreeWeightedOperators
public import LeanFun.Mathlib.Analysis.Normed.Operator.FiniteSection
/-! # Finite boundary rows in weighted coefficient space
Reference: Olver--Townsend (2013), Section 4.1.
-/
@[expose] public noncomputable section
namespace lp
open ContinuousLinearMap

/-- Iterated backward shift removes the first N coordinates. -/
theorem degreeWeightedShiftLeft_pow_apply (s N : ℕ) (x : DegreeWeightedL2 s) (i : ℕ) :
    (((degreeWeightedShiftLeft s)^N) x).1 i = x.1 (i + N) := by
  induction N generalizing i with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', mul_apply_eq_comp, degreeWeightedShiftLeft_apply, ih]
    rw [show i + 1 + N = i + (N + 1) by omega]

/-- Iterated forward shift inserts N zero coordinates. -/
theorem degreeWeightedShiftRight_pow_apply (s N : ℕ) (x : DegreeWeightedL2 s) (i : ℕ) :
    (((degreeWeightedShiftRight s)^N) x).1 i = if i < N then 0 else x.1 (i - N) := by
  induction N generalizing i with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', mul_apply_eq_comp]
    cases i with
    | zero => simp [degreeWeightedShiftRight_zero]
    | succ i =>
      rw [degreeWeightedShiftRight_succ, ih]
      simp only [Nat.add_lt_add_iff_right, Nat.add_sub_add_right]

/-- Deleting and reinserting the first N coordinates gives the complementary projection. -/
theorem degreeWeightedShiftRight_mul_left (s N : ℕ) :
    (degreeWeightedShiftRight s)^N * (degreeWeightedShiftLeft s)^N =
      1 - degreeWeightedProjection s N := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  funext i
  change (((degreeWeightedShiftRight s)^N) (((degreeWeightedShiftLeft s)^N) x)).1 i =
    x.1 i - (degreeWeightedProjection s N x).1 i
  rw [degreeWeightedShiftRight_pow_apply, degreeWeightedProjection_apply]
  split_ifs with hi
  · simp
  · rw [degreeWeightedShiftLeft_pow_apply, Nat.sub_add_cancel (by omega)]
    simp

/-- Weighted truncation is compact. -/
theorem isCompactOperator_degreeWeightedProjection (s N : ℕ) :
    IsCompactOperator (degreeWeightedProjection s N) :=
  isCompactOperator_degreeWeightedTransport s _ (isCompactOperator_coefficientProjection N)

/-- Replace the first N identity rows by the bounded rows of B. -/
def degreeWeightedBoundaryCorrection (s N : ℕ)
    (B : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s) :
    DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s :=
  (degreeWeightedProjection s N).comp (B - 1)

/-- A finite collection of bounded boundary rows gives a compact correction. -/
theorem isCompactOperator_degreeWeightedBoundaryCorrection (s N : ℕ)
    (B : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s) :
    IsCompactOperator (degreeWeightedBoundaryCorrection s N B) :=
  (isCompactOperator_degreeWeightedProjection s N).comp_clm (B - 1)

/-- Bordered remainder for a normalized derivative and lower-order operator. -/
def degreeWeightedBorderedRemainder (s N : ℕ)
    (B A : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s) :
    DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s :=
  degreeWeightedBoundaryCorrection s N B + ((degreeWeightedShiftRight s)^N).comp A

/-- Bordering a compact lower-order operator preserves compactness of the remainder. -/
theorem isCompactOperator_degreeWeightedBorderedRemainder (s N : ℕ)
    (B A : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s) (hA : IsCompactOperator A) :
    IsCompactOperator (degreeWeightedBorderedRemainder s N B A) :=
  (isCompactOperator_degreeWeightedBoundaryCorrection s N B).add
    (hA.clm_comp ((degreeWeightedShiftRight s)^N))

/-- The bordered operator imposes the boundary rows, then the shifted interior rows. -/
theorem degreeWeightedBorderedRemainder_rows (s N : ℕ)
    (B A : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s)
    (x : DegreeWeightedL2 s) (i : ℕ) :
    ((1 + degreeWeightedBorderedRemainder s N B A) x).1 i =
      if i < N then (B x).1 i else x.1 i + (A x).1 (i - N) := by
  change x.1 i + (((degreeWeightedProjection s N) ((B - 1) x)).1 i +
    (((degreeWeightedShiftRight s)^N) (A x)).1 i) = _
  rw [degreeWeightedProjection_apply, degreeWeightedShiftRight_pow_apply]
  split_ifs
  · change x.1 i + (((B x).1 i - x.1 i) + 0) = _
    abel
  · simp
end lp
