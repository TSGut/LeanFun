/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2Norm
public import LeanFun.Mathlib.Analysis.Normed.Lp.CoefficientOperators
public import LeanFun.Mathlib.Analysis.Normed.Lp.Finsupp
/-! # Raw shifted Jacobi coefficients as weighted L² functions

Raw square-summable coefficients synthesize an injectively represented weighted
L² function by multiplying the normalized Hilbert coordinates by sqrt(2/(n+1)).
This map is bounded, but its inverse on the range is not asserted bounded.
Reference: DLMF Table 18.3.1; Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
open MeasureTheory Real Filter
open scoped Topology
namespace Polynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2
local notation "μ" => unitJacobiMeasure 1 0
local notation "b" => hilbertBasisShiftedJacobi (by norm_num : (-1 : ℝ) < 1)
  (by norm_num : (-1 : ℝ) < 0)
local notation "hm" => hasFiniteMoments_unitJacobiMeasure (by norm_num : (-1 : ℝ) < 1)
  (by norm_num : (-1 : ℝ) < 0)
/-- The norm factors of the raw shifted (1,0) basis are uniformly bounded. -/
theorem norm_shiftedJacobiOneZeroScale_le (n : ℕ) : ‖sqrt (2 / ((n : ℝ) + 1))‖ ≤ sqrt 2 := by
  rw [Real.norm_of_nonneg (sqrt_nonneg _)]
  apply sqrt_le_sqrt
  apply div_le_self (by norm_num)
  linarith [Nat.cast_nonneg (α := ℝ) n]
/-- Bounded synthesis of raw coefficients into the shifted (1,0) Jacobi L² space. -/
def shiftedJacobiOneZeroSynthesis : H →L[ℝ] Lp ℝ 2 μ :=
  (b).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (lp.coefficientDiagonal (fun n ↦ sqrt (2 / ((n : ℝ) + 1)))
      (sqrt_nonneg 2) norm_shiftedJacobiOneZeroScale_le)
/-- A raw coordinate vector synthesizes the corresponding unnormalized polynomial. -/
theorem shiftedJacobiOneZeroSynthesis_single (n : ℕ) :
    shiftedJacobiOneZeroSynthesis (lp.single 2 n 1) = polynomialToL2 hm (shiftedJacobi 1 0 n) := by
  have hd : lp.coefficientDiagonal (fun n ↦ sqrt (2 / ((n : ℝ) + 1)))
      (sqrt_nonneg 2) norm_shiftedJacobiOneZeroScale_le (lp.single 2 n 1) =
        sqrt (2 / ((n : ℝ) + 1)) • lp.single 2 n 1 := by
    apply lp.ext
    funext i
    simp only [lp.coefficientDiagonal_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases h : i = n
    · subst i; rfl
    · simp [lp.single_apply, h]
  have hn : (shiftedJacobiSequence (by norm_num : (-1 : ℝ) < 1)
      (by norm_num : (-1 : ℝ) < 0)).squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _
        ((hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _)) = 2 / ((n : ℝ) + 1) := by
    simpa only [Sequence.squaredNorm, shiftedJacobiSequence_apply, integralInner, ← sq]
      using integral_sq_shiftedJacobi_one_zero n
  have hs : sqrt (2 / ((n : ℝ) + 1)) ≠ 0 := (sqrt_pos.mpr (by positivity)).ne'
  rw [shiftedJacobiOneZeroSynthesis, ContinuousLinearMap.comp_apply, hd]
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    map_smul, HilbertBasis.repr_symm_single, hilbertBasisShiftedJacobi_apply,
    Sequence.normalizedToL2, hn, shiftedJacobiSequence_apply, smul_smul,
    mul_inv_cancel₀ hs, one_smul]
/-- No nonzero raw square-summable coefficient vector represents the zero function. -/
theorem shiftedJacobiOneZeroSynthesis_injective : Function.Injective shiftedJacobiOneZeroSynthesis := by
  intro u v h
  have hd := (b).repr.symm.injective h
  apply lp.ext
  funext n
  have he := congrArg (fun w : H ↦ w n) hd
  exact mul_left_cancel₀ (show sqrt (2 / ((n : ℝ) + 1)) ≠ 0 from
    (sqrt_pos.mpr (by positivity)).ne') he
/-- Raw synthesis agrees with polynomial synthesis for every finite coefficient vector. -/
theorem shiftedJacobiOneZeroSynthesis_finsupp (c : ℕ →₀ ℝ) :
    shiftedJacobiOneZeroSynthesis (lp.finsuppL2 c) =
      polynomialToL2 hm (Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single n a =>
    rw [show Finsupp.single n a = a • Finsupp.single n (1 : ℝ) by simp,
      map_smul, map_smul, lp.finsuppL2_single, shiftedJacobiOneZeroSynthesis_single]
    simp only [map_smul, Finsupp.linearCombination_single, one_smul]
/-- Coefficient truncations converge to their weighted function realization. -/
theorem tendsto_shiftedJacobiOneZeroSynthesis_projection (u : H) :
    Tendsto (fun N ↦ shiftedJacobiOneZeroSynthesis (lp.coefficientProjection N u)) atTop
      (𝓝 (shiftedJacobiOneZeroSynthesis u)) :=
  shiftedJacobiOneZeroSynthesis.continuous.continuousAt.tendsto.comp
    (lp.tendsto_coefficientProjection u)

end Polynomial
