/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClenshawCurtisSeries

/-! # Sharper analytic Clenshaw--Curtis error bounds
Sum only the even coefficient tail to obtain the constant 64/15 and the
parity improvement. Reference: ATAP, Theorem 19.3, equation (19.7).
-/

public section
namespace Polynomial.Chebyshev
open MeasureTheory Set Complex

/-- A geometric majorant summed over even frequencies beyond `2m`. -/
theorem tsum_even_tail_le_geometric {a : ℕ → ℝ} {C q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (ha : ∀ k, |a k| ≤ C * q ^ k) (m : ℕ) :
    (∑' k, |a (2 * (k + (m + 1)))|) ≤ C * q ^ (2 * (m + 1)) / (1 - q ^ 2) := by
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hb (k : ℕ) : |a (2 * k)| ≤ C * (q ^ 2) ^ k := by
    simpa only [← pow_mul] using ha (2 * k)
  simpa only [← pow_mul] using
    tsum_tail_le_geometric (sq_nonneg q) hq2 (fun k ↦ abs_nonneg (a (2 * k))) hb (m + 1)

/-- Geometric coefficient decay and representation give the sharper quadrature
bound, with any even cutoff `2m ≤ N`, `m ≥ 1` (ATAP 19.3). -/
theorem abs_integral_sub_clenshawCurtis_le_geometric_even {N m : ℕ}
    (hN : N ≠ 0) (hm : 2 * m ≤ N) (hm1 : 1 ≤ m)
    {a : ℕ → ℝ} {f : ℝ → ℝ} {C q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ k, |a k| ≤ C * q ^ k)
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1,
      HasSum (fun k : ℕ ↦ a k * (T ℝ k).eval x) (f x)) :
    |(∫ x in (-1 : ℝ)..1, f x) - clenshawCurtis N f| ≤
      (32 / 15) * (C * q ^ (2 * (m + 1)) / (1 - q ^ 2)) := by
  have hs : Summable (fun k ↦ |a k|) :=
    ((summable_geometric_of_lt_one hq hq1).mul_left C).of_norm_bounded
      (fun k ↦ by simpa only [Real.norm_eq_abs, abs_abs] using ha k)
  exact (abs_integral_sub_clenshawCurtis_le_even_tail hN hm hm1 hs hf).trans
    (mul_le_mul_of_nonneg_left (tsum_even_tail_le_geometric hq hq1 ha m) (by norm_num))

/-- The parity-sensitive analytic bound with cutoff `2m ≤ N`. Analyticity and
boundedness are required only on the open Bernstein ellipse (ATAP 19.3). -/
theorem abs_integral_sub_clenshawCurtis_le_of_analytic_cutoff
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    {N m : ℕ} (hN : N ≠ 0) (hm : 2 * m ≤ N) (hm1 : 1 ≤ m) :
    |(∫ x in (-1 : ℝ)..1, (F x).re) - clenshawCurtis N (fun x ↦ (F x).re)| ≤
      64 * M / (15 * ρ ^ (2 * m) * (ρ ^ 2 - 1)) := by
  have hρ0 : 0 < ρ := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans
    (hM 0 (by simpa using ofReal_mem_bernsteinEllipse hρ (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num)))
  have hq : ρ⁻¹ < 1 := (inv_lt_one₀ hρ0).2 hρ
  have hc : ContinuousOn (fun t : ℝ ↦ F t) (Icc (-1) 1) :=
    hF.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun t ht ↦ ofReal_mem_bernsteinEllipse hρ ht)
  have hb (k : ℕ) : |(coefficient (n := k) ⟨(fun t : ℝ ↦ (F t).re), integrable_classicalMeasureT ((Complex.continuous_re.comp_continuousOn hc).mul (by fun_prop))⟩)| ≤
      (2 * M) * (ρ⁻¹) ^ k := by
    rw [← complexCoefficient_re hc]
    apply (abs_re_le_norm _).trans
    apply (norm_complexCoefficient_le_of_analytic hρ hF hM k).trans
    rw [inv_pow, div_eq_mul_inv]
    gcongr
    split_ifs <;> norm_num
  have hs : Summable (fun k ↦ |(coefficient (n := k) ⟨(fun t : ℝ ↦ (F t).re), integrable_classicalMeasureT ((Complex.continuous_re.comp_continuousOn hc).mul (by fun_prop))⟩)|) :=
    ((summable_geometric_of_lt_one (inv_nonneg.mpr hρ0.le) hq).mul_left (2 * M)).of_norm_bounded
      (fun k ↦ by simpa only [Real.norm_eq_abs, abs_abs] using hb k)
  have h := abs_integral_sub_clenshawCurtis_le_geometric_even hN hm hm1
    (inv_nonneg.mpr hρ0.le) hq hb
    (fun x hx ↦ hasSum_coefficient_mul_eval_T (Complex.continuous_re.comp_continuousOn hc) hs hx)
  apply h.trans_eq
  rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add, inv_pow, inv_pow]
  field_simp
  ring

/-- The sharper Clenshaw--Curtis estimate for any `N ≥ 2` (ATAP 19.3). -/
theorem abs_integral_sub_clenshawCurtis_le_sharp_of_analytic
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M) {N : ℕ} (hN : 2 ≤ N) :
    |(∫ x in (-1 : ℝ)..1, (F x).re) - clenshawCurtis N (fun x ↦ (F x).re)| ≤
      64 * M / (15 * ρ ^ (N - 1) * (ρ ^ 2 - 1)) := by
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans
    (hM 0 (by simpa using ofReal_mem_bernsteinEllipse hρ (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num)))
  apply (abs_integral_sub_clenshawCurtis_le_of_analytic_cutoff hρ hF hM
    (N := N) (m := N / 2) (by omega) (by omega) (by omega)).trans
  have he : N - 1 ≤ 2 * (N / 2) := by omega
  have hp : ρ ^ (N - 1) ≤ ρ ^ (2 * (N / 2)) := pow_le_pow_right₀ hρ.le he
  have hd : 0 < ρ ^ 2 - 1 := by nlinarith
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

/-- Even `N` gains a further factor `ρ⁻¹` (ATAP 19.3). -/
theorem abs_integral_sub_clenshawCurtis_le_sharp_of_analytic_even
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M) {N : ℕ}
    (hN : 2 ≤ N) (he : Even N) :
    |(∫ x in (-1 : ℝ)..1, (F x).re) - clenshawCurtis N (fun x ↦ (F x).re)| ≤
      64 * M / (15 * ρ ^ N * (ρ ^ 2 - 1)) := by
  obtain ⟨m, rfl⟩ := he
  simpa only [two_mul] using abs_integral_sub_clenshawCurtis_le_of_analytic_cutoff hρ hF hM
    (N := m + m) (m := m) (by omega) (by omega) (by omega)

end Polynomial.Chebyshev
