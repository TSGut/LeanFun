/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClenshawCurtisModes
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Clenshaw--Curtis error as an even coefficient tail
Termwise integration and quadrature are justified by absolute summability.
Reference: ATAP, proof of Theorem 19.3.
-/

public section
namespace Polynomial.Chebyshev
open MeasureTheory Set

/-- Absolute coefficient summability permits integration of a Chebyshev series. -/
theorem hasSum_integralMoment {a : ℕ → ℝ} {f : ℝ → ℝ}
    (ha : Summable (fun k ↦ |a k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1,
      HasSum (fun k : ℕ ↦ a k * (T ℝ k).eval x) (f x)) :
    HasSum (fun k ↦ a k * integralMoment k) (∫ x in (-1 : ℝ)..1, f x) := by
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (-1 : ℝ)) (b := 1) (μ := volume)
    (F := fun k x ↦ a k * (T ℝ k).eval x) (f := f) (fun k _ ↦ |a k|)
    (fun k ↦ (continuous_const.mul (T ℝ k).continuous).aestronglyMeasurable)
    (fun k ↦ Filter.Eventually.of_forall fun x hx ↦ by
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using uIoc_subset_uIcc hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_eval_T_real_le_one _ (abs_le.mpr hx')))
    (Filter.Eventually.of_forall fun _ _ ↦ ha) intervalIntegrable_const
    (Filter.Eventually.of_forall fun x hx ↦ hf x (by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using uIoc_subset_uIcc hx))
  simpa only [intervalIntegral.integral_const_mul, ← integralMoment_eq_integral] using h

/-- Quadrature commutes with any series summable at its nodes. -/
theorem hasSum_clenshawCurtis {N : ℕ} (hN : N ≠ 0) {a : ℕ → ℝ} {f : ℝ → ℝ}
    (hf : ∀ j ≤ N,
      HasSum (fun k : ℕ ↦ a k * (T ℝ k).eval (node N j)) (f (node N j))) :
    HasSum (fun k ↦ a k * clenshawCurtis N (fun x ↦ (T ℝ k).eval x))
      (clenshawCurtis N f) := by
  simp_rw [clenshawCurtis_eq_sum_weights ⟨N, Nat.pos_of_ne_zero hN⟩, Finset.mul_sum]
  simpa only [mul_left_comm, classicalNode] using
    hasSum_sum (s := (Finset.univ : Finset (Fin (N + 1))))
      (fun j hj ↦ (hf j (Nat.le_of_lt_succ j.isLt)).mul_left (clenshawCurtisWeight ⟨N, Nat.pos_of_ne_zero hN⟩ j))

/-- Only even coefficients above the exactness degree contribute to the error.
The integer `m` may be any cutoff with `2m ≤ N`. -/
theorem hasSum_clenshawCurtis_error_even_tail {N m : ℕ} (hN : N ≠ 0) (hm : 2 * m ≤ N)
    {a : ℕ → ℝ} {f : ℝ → ℝ} (ha : Summable (fun k ↦ |a k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1,
      HasSum (fun k : ℕ ↦ a k * (T ℝ k).eval x) (f x)) :
    HasSum (fun k ↦ a (2 * (k + (m + 1))) *
      (integralMoment (2 * (k + (m + 1))) -
        clenshawCurtis N (fun x ↦ (T ℝ (↑(2 * (k + (m + 1)) : ℕ))).eval x)))
      ((∫ x in (-1 : ℝ)..1, f x) - clenshawCurtis N f) := by
  let d (k : ℕ) := a k *
    (integralMoment k - clenshawCurtis N (fun x ↦ (T ℝ k).eval x))
  have hs : HasSum d ((∫ x in (-1 : ℝ)..1, f x) - clenshawCurtis N f) := by
    simpa only [d, mul_sub] using
      (hasSum_integralMoment ha hf).sub (hasSum_clenshawCurtis hN (fun j _ ↦ hf _ node_mem_Icc))
  have he : Summable (fun k ↦ d (2 * k)) :=
    hs.summable.comp_injective (fun _ _ h ↦ by omega)
  have ho : ∀ k, d (2 * k + 1) = 0 := by
    intro k
    simp only [d, integralMoment_odd, clenshawCurtis_eval_T_odd hN, sub_self, mul_zero]
  have heq : (∑' k, d (2 * k)) = (∫ x in (-1 : ℝ)..1, f x) - clenshawCurtis N f := by
    have ht := tsum_even_add_odd he (hs.summable.comp_injective (fun _ _ h ↦ by omega))
    simpa only [ho, tsum_zero, add_zero, hs.tsum_eq] using ht
  have hz : ∑ k ∈ Finset.range (m + 1), d (2 * k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkN : 2 * k ≤ N := by simp only [Finset.mem_range] at hk; omega
    have hp : (T ℝ (↑(2 * k : ℕ))).degree ≤ N := by
      simpa only [degree_T, Int.natAbs_natCast, Nat.cast_le] using hkN
    simp only [d, clenshawCurtis_eval hN hp, ← integralMoment_eq_integral, sub_self, mul_zero]
  have ht := he.sum_add_tsum_nat_add (m + 1)
  rw [hz, zero_add, heq] at ht
  exact ht ▸ ((summable_nat_add_iff (m + 1)).2 he).hasSum

/-- The ATAP mode bound reduces quadrature error to the unresolved even tail. -/
theorem abs_integral_sub_clenshawCurtis_le_even_tail {N m : ℕ}
    (hN : N ≠ 0) (hm : 2 * m ≤ N) (hm1 : 1 ≤ m)
    {a : ℕ → ℝ} {f : ℝ → ℝ} (ha : Summable (fun k ↦ |a k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1,
      HasSum (fun k : ℕ ↦ a k * (T ℝ k).eval x) (f x)) :
    |(∫ x in (-1 : ℝ)..1, f x) - clenshawCurtis N f| ≤
      (32 / 15) * ∑' k, |a (2 * (k + (m + 1)))| := by
  have hs := hasSum_clenshawCurtis_error_even_tail hN hm ha hf
  have ht : Summable (fun k ↦ |a (2 * (k + (m + 1)))|) :=
    ha.comp_injective (fun _ _ h ↦ by omega)
  have hb (k : ℕ) : ‖a (2 * (k + (m + 1))) *
      (integralMoment (2 * (k + (m + 1))) -
        clenshawCurtis N (fun x ↦ (T ℝ (↑(2 * (k + (m + 1)) : ℕ))).eval x))‖ ≤
      (32 / 15) * |a (2 * (k + (m + 1)))| := by
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (abs_integralMoment_sub_clenshawCurtis_le hN (by omega)) (abs_nonneg _)
  rw [← hs.tsum_eq, ← Real.norm_eq_abs, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (hs.summable.norm)).trans
    (hs.summable.norm.tsum_le_tsum hb (ht.mul_left _))

end Polynomial.Chebyshev
