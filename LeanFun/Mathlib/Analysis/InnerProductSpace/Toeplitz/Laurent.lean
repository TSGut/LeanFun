/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Laurent-polynomial Toeplitz operators

Positive monomials act by forward shifts and negative monomials by backward
shifts. The resulting symbol map is linear; boundary effects prevent it from
being an algebra homomorphism. Reference: Böttcher–Silbermann, Introduction to
Large Truncated Toeplitz Matrices, Chapter 1.
-/

@[expose] public noncomputable section
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]
local notation "H" => lp (fun _ : ℕ ↦ 𝕜) 2

/-- The one-sided shift corresponding to a Laurent monomial. -/
def laurentShiftL2 : ℤ → (H →L[𝕜] H)
  | .ofNat n => forwardShiftL2.toContinuousLinearMap ^ n
  | .negSucc n => backwardShiftL2 ^ (n+1)

/-- Every signed shift has constant matrix diagonals. -/
theorem isToeplitz_laurentShiftL2 (k : ℤ) :
    IsToeplitz (laurentShiftL2 (𝕜 := 𝕜) k) := by
  cases k with
  | ofNat n => exact isToeplitz_forwardShiftL2_pow n
  | negSucc n => exact isToeplitz_backwardShiftL2_pow (n+1)

/-- Signed shifts are contractions. -/
theorem norm_laurentShiftL2_le (k : ℤ) : ‖laurentShiftL2 (𝕜 := 𝕜) k‖ ≤ 1 := by
  have hS : ‖(forwardShiftL2 (𝕜 := 𝕜)).toContinuousLinearMap‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  have hB : ‖backwardShiftL2 (𝕜 := 𝕜)‖ ≤ 1 := by
    simpa only [backwardShiftL2, LinearIsometryEquiv.norm_map] using hS
  have hp (A : H →L[𝕜] H) (hA : ‖A‖ ≤ 1) (n : ℕ) : ‖A^n‖ ≤ 1 := by
    induction n with
    | zero =>
      rw [pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg A])
  cases k with
  | ofNat n => exact hp _ hS n
  | negSucc n => exact hp _ hB (n+1)

/-- The linear Toeplitz quantization of a Laurent polynomial. -/
def laurentToeplitz : LaurentPolynomial 𝕜 →ₗ[𝕜] (H →L[𝕜] H) where
  toFun p := Finsupp.linearCombination 𝕜 laurentShiftL2 p.coeff
  map_add' p q := by simp
  map_smul' c p := by simp

/-- Quantization is the finite sum of the coefficient-weighted shifts. -/
theorem laurentToeplitz_apply (p : LaurentPolynomial 𝕜) :
    laurentToeplitz p = p.coeff.sum (fun k a ↦ a • laurentShiftL2 k) := rfl

/-- The coefficient ℓ¹ norm bounds the Toeplitz operator norm. -/
theorem norm_laurentToeplitz_le (p : LaurentPolynomial 𝕜) :
    ‖laurentToeplitz p‖ ≤ ∑ k ∈ p.coeff.support, ‖p.coeff k‖ := by
  rw [laurentToeplitz_apply, Finsupp.sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_laurentShiftL2_le k)

/-- A monomial gives its signed shift, with its scalar coefficient. -/
theorem laurentToeplitz_single (k : ℤ) (a : 𝕜) :
    laurentToeplitz (AddMonoidAlgebra.single k a) = a • laurentShiftL2 k := by
  change Finsupp.linearCombination 𝕜 laurentShiftL2 (Finsupp.single k a) = _
  simp

/-- Laurent-polynomial quantization always gives a bounded Toeplitz operator. -/
theorem isToeplitz_laurentToeplitz (p : LaurentPolynomial 𝕜) :
    IsToeplitz (laurentToeplitz p) := by
  change laurentToeplitz p ∈ toeplitzSubmodule
  rw [laurentToeplitz_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.smul_mem _ _ (isToeplitz_laurentShiftL2 k)

/-- The basic multiplicative defect is precisely the boundary projection. -/
theorem laurentShiftL2_mul_neg_one :
    laurentShiftL2 (𝕜 := 𝕜) 1 * laurentShiftL2 (-1) = 1-initialL2Projection 1 := by
  change forwardShiftL2.toContinuousLinearMap ^ 1 * backwardShiftL2 ^ 1 = _
  rw [pow_one, pow_one]
  exact forwardShiftL2_comp_backwardShiftL2

/-- The basic multiplicative defect is compact. -/
theorem isCompactOperator_laurentShiftL2_defect :
    IsCompactOperator (fun u : H ↦
      ((1 - laurentShiftL2 1 * laurentShiftL2 (-1)) : H →L[𝕜] H) u) := by
  rw [laurentShiftL2_mul_neg_one, sub_sub_cancel]
  exact isCompactOperator_initialL2Projection 1

end lp
