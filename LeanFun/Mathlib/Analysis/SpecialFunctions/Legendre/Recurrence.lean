/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Legendre.Structure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Legendre recurrence and Christoffel–Darboux identities

We specialise the general orthogonal-polynomial recurrence, then transfer its
rational polynomial identity to arbitrary rational algebras.
References: DLMF 18.2.12 and Table 18.9.1.
-/
public section
open MeasureTheory
namespace Polynomial

/-- The forward Legendre recurrence coefficient (DLMF Table 18.9.1). -/
theorem recurrenceA_legendreSequence (n : ℕ) :
    (legendreSequence ℝ).recurrenceA n = (n + 1 : ℝ) / (2 * n + 1) := by
  have h := coeff_derivative_legendre_succ ℝ n
  rw [coeff_derivative] at h
  have hl : (legendre ℝ (n + 1)).leadingCoeff * (n + 1 : ℝ) =
      (2 * n + 1 : ℝ) * (legendre ℝ n).leadingCoeff := by
    simpa only [leadingCoeff, natDegree_legendre] using h
  unfold Sequence.recurrenceA
  simp only [legendreSequence_apply]
  apply (div_eq_div_iff (leadingCoeff_ne_zero.mpr ((legendreSequence ℝ).ne_zero (n + 1)))
    (by positivity : (2 * n + 1 : ℝ) ≠ 0)).2
  simp only [legendreSequence_apply]
  nlinarith [hl]

/-- The diagonal Legendre recurrence coefficient vanishes by parity (DLMF Table 18.9.1). -/
theorem recurrenceB_legendreSequence (n : ℕ) :
    (legendreSequence ℝ).recurrenceB legendreMeasure n (Sequence.RecurrenceBInput.of _ _ _) = 0 := by
  have hodd (x : ℝ) : (-x) * (legendre ℝ n).eval (-x) ^ 2 =
      -(x * (legendre ℝ n).eval x ^ 2) := by
    rw [eval_legendre_neg, mul_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hi := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun x : ℝ ↦ x * (legendre ℝ n).eval x ^ 2)
  simp only [hodd, intervalIntegral.integral_neg, neg_neg] at hi
  have hz : ∫ x in (-1 : ℝ)..1, x * (legendre ℝ n).eval x ^ 2 = 0 := by linarith
  unfold Sequence.recurrenceB integralInner
  simp only [legendreSequence_apply, eval_mul, eval_X, mul_assoc, ← pow_two]
  have hz' : (∫ x, x * (legendre ℝ n).eval x ^ 2 ∂legendreMeasure) = 0 := by
    rw [legendreMeasure, ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num), hz]
  rw [hz', zero_div]

/-- The backward Legendre recurrence coefficient (DLMF Table 18.9.1). -/
theorem recurrenceC_legendreSequence (n : ℕ) :
    (legendreSequence ℝ).recurrenceC legendreMeasure n (Sequence.RecurrenceCInput.of _ _ _) = (n + 1 : ℝ) / (2 * n + 3) := by
  rw [Sequence.recurrenceC, recurrenceA_legendreSequence, squaredNorm_legendreSequence,
    squaredNorm_legendreSequence]
  push_cast
  field_simp
  ring

private theorem legendre_recurrence_real (n : ℕ) :
    C (n + 2 : ℝ) * legendre ℝ (n + 2) =
      C (2 * n + 3 : ℝ) * X * legendre ℝ (n + 1) - C (n + 1 : ℝ) * legendre ℝ n := by
  have h := isOrthogonal_legendreSequence.three_term hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure n
  rw [recurrenceA_legendreSequence, recurrenceB_legendreSequence, recurrenceC_legendreSequence] at h
  simp only [legendreSequence_apply, zero_smul, add_zero, smul_eq_C_mul] at h
  push_cast at h
  have h' := congrArg (fun p : ℝ[X] ↦ C (2 * n + 3 : ℝ) * p) h
  have hd : (2 * ((n : ℝ) + 1) + 1) = 2 * n + 3 := by ring
  rw [hd] at h'
  simp only [mul_add, ← mul_assoc, ← C_mul] at h'
  have hz : (2 * n + 3 : ℝ) ≠ 0 := by positivity
  simp only [mul_div_cancel₀ _ hz] at h'
  simp only [map_add, map_one, map_ofNat] at h' ⊢
  linear_combination -h'

/-- The cleared three-term recurrence over every commutative rational algebra
(DLMF Table 18.9.1). -/
theorem legendre_recurrence (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    C (n + 2 : R) * legendre R (n + 2) =
      C (2 * n + 3 : R) * X * legendre R (n + 1) - C (n + 1 : R) * legendre R n := by
  have hq : C (n + 2 : ℚ) * legendre ℚ (n + 2) =
      C (2 * n + 3 : ℚ) * X * legendre ℚ (n + 1) - C (n + 1 : ℚ) * legendre ℚ n := by
    apply (map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective)
    simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
      map_X, map_legendre_rat, map_add, map_mul, map_natCast, map_ofNat, map_one,
      Polynomial.map_add, Polynomial.map_natCast, Polynomial.map_ofNat, Polynomial.map_one] using
      legendre_recurrence_real n
  have h := congrArg (Polynomial.map (algebraMap ℚ R)) hq
  simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
    map_X, map_legendre_rat, map_add, map_mul, map_natCast, map_ofNat, map_one,
      Polynomial.map_add, Polynomial.map_natCast, Polynomial.map_ofNat, Polynomial.map_one] using h

/-- The Legendre Christoffel–Darboux identity, with `x-y` cleared (DLMF 18.2.12). -/
theorem legendre_christoffelDarboux (n : ℕ) (x y : ℝ) :
    (x - y) * ∑ k ∈ Finset.range (n + 1), ((2 * k + 1 : ℝ) / 2) *
      (legendre ℝ k).eval x * (legendre ℝ k).eval y =
    ((n + 1 : ℝ) / 2) * ((legendre ℝ (n + 1)).eval x * (legendre ℝ n).eval y -
      (legendre ℝ n).eval x * (legendre ℝ (n + 1)).eval y) := by
  have h := isOrthogonal_legendreSequence.christoffelDarboux hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure n x y
  simp only [Sequence.kernel_of_positive (hasPositiveDefiniteIntegral_legendreMeasure) (legendreSequence ℝ), legendreSequence_apply, squaredNorm_legendreSequence,
    recurrenceA_legendreSequence] at h
  have hc : ((n + 1 : ℝ) / (2 * n + 1)) / (2 / (2 * n + 1)) = (n + 1) / 2 := by field_simp
  rw [hc] at h
  convert h using 2
  congr 1
  funext k
  field_simp

/-- The diagonal Legendre Christoffel–Darboux identity (DLMF 18.2.13). -/
theorem legendre_christoffelDarboux_diag (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n + 1), ((2 * k + 1 : ℝ) / 2) * (legendre ℝ k).eval x ^ 2) =
    ((n + 1 : ℝ) / 2) * ((legendre ℝ (n + 1)).derivative.eval x * (legendre ℝ n).eval x -
      (legendre ℝ n).derivative.eval x * (legendre ℝ (n + 1)).eval x) := by
  have h := isOrthogonal_legendreSequence.christoffelDarboux_diag hasFiniteMoments_legendreMeasure
    hasPositiveDefiniteIntegral_legendreMeasure n x
  simp only [Sequence.kernel_of_positive (hasPositiveDefiniteIntegral_legendreMeasure) (legendreSequence ℝ), legendreSequence_apply, squaredNorm_legendreSequence,
    recurrenceA_legendreSequence] at h
  have hc : ((n + 1 : ℝ) / (2 * n + 1)) / (2 / (2 * n + 1)) = (n + 1) / 2 := by field_simp
  rw [hc] at h
  convert h using 2
  field_simp

end Polynomial
