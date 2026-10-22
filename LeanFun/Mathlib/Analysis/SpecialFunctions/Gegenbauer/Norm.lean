/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Norm

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Gegenbauer squared norms
Transfer the Jacobi squared norms and simplify with the Gamma duplication formula.
The degree-zero formula also covers parameter zero. Reference: DLMF Table 18.3.1.
-/

public section
open MeasureTheory Real
namespace Polynomial

/-- Squared norms transfer with the square of the bridge factor (DLMF 18.7.1). -/
theorem integral_sq_gegenbauer_eq_jacobi {lam : ℝ} (hlam : -(1 / 2) < lam) (n : ℕ) :
    (∫ x, (gegenbauer lam n).eval x ^ 2 ∂gegenbauerMeasure lam) =
      ((ascPochhammer ℝ n).eval (2 * lam) /
        (ascPochhammer ℝ n).eval (lam + 1 / 2)) ^ 2 *
          ∫ x, (jacobi (lam - 1 / 2) (lam - 1 / 2) n).eval x ^ 2
            ∂jacobiMeasure (lam - 1 / 2) (lam - 1 / 2) := by
  rw [gegenbauerMeasure_eq_jacobiMeasure]
  simp_rw [gegenbauer_eq_jacobi_mul hlam, eval_mul, eval_C, mul_pow]
  exact integral_const_mul _ _

private theorem gamma_ne_zero_of_neg_one_lt {s : ℝ} (hs : -1 < s) (hzero : s ≠ 0) :
    Gamma s ≠ 0 := by
  have h := (Gamma_pos_of_pos (show 0 < s + 1 by linarith)).ne'
  rw [Gamma_add_one hzero] at h
  exact (mul_ne_zero_iff.mp h).2

private theorem gamma_add_nat {s : ℝ} (hs : -1 < s) (hzero : s ≠ 0) (n : ℕ) :
    Gamma (s + n) = (ascPochhammer ℝ n).eval s * Gamma s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : s + n ≠ 0 := by
      rcases n with _ | n
      · simpa using hzero
      · have : 0 < s + (n + 1 : ℕ) := by
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) n]
        exact this.ne'
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Gamma_add_one hn, ih,
      ascPochhammer_succ_eval]
    ring

private theorem pochhammer_eq_gamma_div {s : ℝ} (hs : -1 < s) (hzero : s ≠ 0) (n : ℕ) :
    (ascPochhammer ℝ n).eval s = Gamma (s + n) / Gamma s := by
  rw [gamma_add_nat hs hzero, mul_div_cancel_right₀ _ (gamma_ne_zero_of_neg_one_lt hs hzero)]

/-- The degree-zero norm is nonsingular even at parameter zero (DLMF Table 18.3.1). -/
private theorem integral_sq_gegenbauer_zero_gamma_formula {lam : ℝ} (hlam : -(1 / 2) < lam) :
    ∫ x, (gegenbauer lam 0).eval x ^ 2 ∂gegenbauerMeasure lam =
      √π * Gamma (lam + 1 / 2) / Gamma (lam + 1) := by
  have ha : -1 < lam - 1 / 2 := by linarith
  rw [integral_sq_gegenbauer_eq_jacobi hlam]
  simp only [ascPochhammer_zero, eval_one, div_self (one_ne_zero : (1 : ℝ) ≠ 0),
    one_pow, one_mul]
  rw [integral_sq_jacobi_zero ha ha]
  simp only [GammaOn, GammaPoint.ofPos]
  have harg : lam - 1 / 2 + (lam - 1 / 2) + 1 = 2 * lam := by ring
  have harg2 : lam - 1 / 2 + (lam - 1 / 2) + 2 = 2 * lam + 1 := by ring
  have harg3 : lam - 1 / 2 + 1 = lam + 1 / 2 := by ring
  rw [harg, harg2, harg3]
  have hd := Gamma_mul_Gamma_add_half (lam + 1 / 2)
  rw [show lam + 1 / 2 + 1 / 2 = lam + 1 by ring,
    show 2 * (lam + 1 / 2) = 2 * lam + 1 by ring,
    show 1 - (2 * lam + 1) = -(2 * lam) by ring, Real.rpow_neg (by norm_num)] at hd
  have hg1 := (Gamma_pos_of_pos (show 0 < lam + 1 by linarith)).ne'
  have hg2 := (Gamma_pos_of_pos (show 0 < 2 * lam + 1 by linarith)).ne'
  have hp := (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 * lam)).ne'
  apply (div_eq_div_iff hg2 hg1).2
  calc
    _ = Gamma (lam + 1 / 2) * (Gamma (lam + 1 / 2) * Gamma (lam + 1)) *
        (2 : ℝ) ^ (2 * lam) := by ring
    _ = Gamma (lam + 1 / 2) *
        (Gamma (2 * lam + 1) * ((2 : ℝ) ^ (2 * lam))⁻¹ * √π) *
          (2 : ℝ) ^ (2 * lam) := by rw [hd]
    _ = _ := by field_simp

/-- The positive-degree norm in the standard Gamma normalisation (DLMF Table 18.3.1). -/
private theorem integral_sq_gegenbauer_succ_gamma_formula {lam : ℝ} (hlam : -(1 / 2) < lam)
    (hzero : lam ≠ 0) (n : ℕ) :
    ∫ x, (gegenbauer lam (n + 1)).eval x ^ 2 ∂gegenbauerMeasure lam =
      (2 : ℝ) ^ (1 - 2 * lam) * π * Gamma (n + 1 + 2 * lam) /
        (((n : ℝ) + 1 + lam) * Gamma lam ^ 2 * (n + 1).factorial) := by
  have ha : -1 < lam - 1 / 2 := by linarith
  have h2 : 2 * lam ≠ 0 := mul_ne_zero (by norm_num) hzero
  have hh : 0 < lam + 1 / 2 := by linarith
  have hn : 0 < (n : ℝ) + 1 + 2 * lam := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnh : 0 < (n : ℝ) + 1 + lam := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hng : 0 < (n : ℝ) + lam + 3 / 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hg := gamma_ne_zero_of_neg_one_lt (by linarith : -1 < lam) hzero
  have hg2 := gamma_ne_zero_of_neg_one_lt (by linarith : -1 < 2 * lam) h2
  have hgh := (Gamma_pos_of_pos hh).ne'
  have hgn := (Gamma_pos_of_pos hn).ne'
  have hgnh := (Gamma_pos_of_pos hng).ne'
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [integral_sq_gegenbauer_eq_jacobi hlam, integral_sq_jacobi_succ ha ha,
    pochhammer_eq_gamma_div (by linarith : -1 < 2 * lam) h2,
    pochhammer_eq_gamma_div (by linarith : -1 < lam + 1 / 2) hh.ne']
  simp only [GammaOn, GammaPoint.ofPos]
  rw [show lam - 1 / 2 + (lam - 1 / 2) + 1 = 2 * lam by ring,
    show (n : ℝ) + (lam - 1 / 2) + 2 = n + lam + 3 / 2 by ring,
    show (n : ℝ) + (lam - 1 / 2) + (lam - 1 / 2) + 2 = n + 1 + 2 * lam by ring,
    show 2 * (n : ℝ) + (lam - 1 / 2) + (lam - 1 / 2) + 3 =
      2 * (n + 1 + lam) by ring]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show 2 * lam + ((n : ℝ) + 1) = n + 1 + 2 * lam by ring,
    show lam + 1 / 2 + ((n : ℝ) + 1) = n + lam + 3 / 2 by ring]
  have hd := Gamma_mul_Gamma_add_half lam
  have hhalf : Gamma (lam + 1 / 2) =
      Gamma (2 * lam) * (2 : ℝ) ^ (1 - 2 * lam) * √π / Gamma lam := by
    apply (eq_div_iff hg).2
    nlinarith [hd]
  have hp : (2 : ℝ) ^ (2 * lam) * (2 : ℝ) ^ (1 - 2 * lam) = 2 := by
    rw [← Real.rpow_add (by norm_num), add_sub_cancel, Real.rpow_one]
  have hgnorm : Gamma ((2 * ((n : ℝ) + lam) + 3) / 2) ≠ 0 :=
    (Gamma_pos_of_pos (by linarith)).ne'
  rw [hhalf]
  field_simp [hgnorm]
  rw [Real.sq_sqrt pi_pos.le]
  linear_combination π * hp

/-- The classical Gamma formula; every displayed Gamma value excludes its poles. -/
theorem integral_sq_gegenbauer_zero {lam : ℝ} (hlam : -(1 / 2) < lam) :
    ∫ x, (gegenbauer lam 0).eval x ^ 2 ∂gegenbauerMeasure lam =
      √π * GammaOn (GammaPoint.ofPos (lam + 1 / 2) (by linarith)) / GammaOn (GammaPoint.ofPos (lam + 1) (by linarith)) :=
  integral_sq_gegenbauer_zero_gamma_formula hlam

/-- The classical Gamma formula; every displayed Gamma value excludes its poles. -/
theorem integral_sq_gegenbauer_succ {lam : ℝ} (hlam : -(1 / 2) < lam)
    (hzero : lam ≠ 0) (n : ℕ) :
    ∫ x, (gegenbauer lam (n + 1)).eval x ^ 2 ∂gegenbauerMeasure lam =
      (2 : ℝ) ^ (1 - 2 * lam) * π * GammaOn (GammaPoint.ofPos (n + 1 + 2 * lam) (by have _hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)) /
        (((n : ℝ) + 1 + lam) * GammaOn ⟨lam, by
          intro m he
          cases m with
          | zero => exact hzero (by simpa using he)
          | succ m =>
            have _hm := Nat.cast_nonneg (α := ℝ) m
            push_cast at he
            linarith⟩ ^ 2 * (n + 1).factorial) :=
  integral_sq_gegenbauer_succ_gamma_formula hlam hzero n

end Polynomial
