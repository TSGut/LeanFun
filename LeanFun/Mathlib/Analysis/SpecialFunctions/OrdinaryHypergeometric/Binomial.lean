/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Analytic.Binomial

/-! # The binomial series in Pochhammer normalization

The coefficients used in Euler's hypergeometric integral, DLMF 15.6.1,
are the existing binomial series coefficients, written as `(a)_n / n!`.
-/

public section
open scoped ENNReal NNReal
open Polynomial
namespace Complex

/-- Pochhammer normalization of the generalized binomial coefficient. -/
theorem choose_add_nat_sub_one_eq (a : ℂ) (n : ℕ) :
    Ring.choose (a+n-1) n = (n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a := by
  rw [← Ring.multichoose_eq]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  simp only [nsmul_eq_mul] at h
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply (mul_left_cancel₀ hn)
  rw [h, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  exact Polynomial.ascPochhammer_smeval_eq_eval a n

/-- The binomial expansion on the unit disk, with the coefficients needed by
Euler's integral (DLMF 15.6.1). -/
theorem hasSum_pochhammer_mul_pow (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ ((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a) * z^n)
      (1 / (1-z)^a) := by
  have h := (one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).hasSum
    (y := z) (by
      rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
      exact_mod_cast hz)
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    choose_add_nat_sub_one_eq, zero_add] using h

/-- Absolute convergence of the Pochhammer binomial expansion inside its disk. -/
theorem summable_norm_pochhammer_mul_pow (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ ↦ ‖((n.factorial : ℂ)⁻¹ *
      (ascPochhammer ℂ n).eval a) * z^n‖) := by
  have h := one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a
  have hr : (‖z‖₊ : ℝ≥0∞) < 1 := by exact_mod_cast hz
  have hs := h.r_le
  have hsum := (FormalMultilinearSeries.ofScalars ℂ
    (fun n ↦ Ring.choose (a+n-1) n)).summable_norm_apply (x := z)
      (by simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm] using hr.trans_le hs)
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    choose_add_nat_sub_one_eq] using hsum

end Complex
