/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Complex.BernsteinEllipse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Chebyshev growth on Bernstein ellipses
The Joukowski formula bounds the degree-n polynomial by the nth power of the
ellipse parameter. Reference: ATAP, Chapter 8, Exercise 8.8.
-/

public section
namespace Polynomial.Chebyshev
open Complex

/-- The Joukowski formula for complex Chebyshev polynomials (ATAP, Chapter 8). -/
theorem eval_T_joukowski (w : {z : ℂ // z ≠ 0}) (n : ℕ) :
    (T ℂ n).eval (joukowski w) = (w.val ^ n + w.val⁻¹ ^ n) / 2 := by
  have hw := w.property
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [joukowski]
  | more n hn hn1 =>
    rw [Nat.cast_add, Nat.cast_ofNat, T_add_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [show (n : ℤ) + 1 = ↑(n + 1 : ℕ) by omega, hn, hn1]
    simp only [joukowski, pow_succ]
    field_simp
    ring

/-- Chebyshev growth inside an open ellipse (ATAP, Exercise 8.8). -/
theorem norm_eval_T_le_on_bernsteinEllipse {r : ℝ} (hr : 1 < r) {z : ℂ}
    (hz : z ∈ bernsteinEllipse ⟨r, hr⟩) (n : ℕ) : ‖(T ℂ n).eval z‖ ≤ r ^ n := by
  rw [bernsteinEllipse_eq_image_annulus hr] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hr0 : 0 < r := by linarith
  have hw0 : 0 < ‖w.val‖ := lt_trans (inv_pos.mpr hr0) hw.1
  have hi : ‖w.val‖⁻¹ < r := (inv_lt_comm₀ hw0 hr0).2 hw.1
  rw [eval_T_joukowski w, norm_div, norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have hn := norm_add_le (w.val ^ n) (w.val⁻¹ ^ n)
  rw [norm_pow, norm_pow, norm_inv] at hn
  have h1 := pow_le_pow_left₀ (norm_nonneg w.val) hw.2.le n
  have h2 := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg w.val)) hi.le n
  linarith

end Polynomial.Chebyshev
