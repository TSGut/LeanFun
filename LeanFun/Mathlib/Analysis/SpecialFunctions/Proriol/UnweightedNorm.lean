/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.PolynomialMoments
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Norm

/-! # Elementary norms on the unweighted Proriol triangle

Gamma factors cancel when the first Jacobi parameter is zero, yielding the
rational triangle norm. Reference: DLMF Table 18.3.1 and 18.37.8.
-/

public section
open MeasureTheory Real
namespace Polynomial

/-- Jacobi norms with first parameter zero need no Gamma factors. -/
theorem integral_sq_jacobi_zero_left {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    (∫ x, (jacobi 0 β n).eval x ^ 2 ∂jacobiMeasure 0 β) =
      (2 : ℝ)^(β+1)/(2*n+β+1) := by
  cases n with
  | zero =>
    rw [integral_sq_jacobi_zero (by norm_num) hβ]
    simp only [GammaOn, GammaPoint.ofPos, zero_add, Nat.cast_zero, mul_zero, Gamma_one, mul_one]
    rw [show β+2 = (β+1)+1 by ring, Gamma_add_one (by linarith : β+1 ≠ 0)]
    have hg : Gamma (β+1) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
    field_simp
  | succ n =>
    rw [integral_sq_jacobi_succ (by norm_num) hβ]
    simp only [GammaOn, GammaPoint.ofPos, zero_add, add_zero]
    rw [show (n : ℝ)+2 = (n+1 : ℕ)+1 by push_cast; ring, Gamma_nat_eq_factorial]
    have hg : Gamma ((n : ℝ)+β+2) ≠ 0 :=
      (Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)).ne'
    have hf : ((n+1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hd : 2*(n : ℝ)+β+3 ≠ 0 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    simp only [Nat.cast_succ]
    field_simp
    ring

end Polynomial
namespace MvPolynomial
open Polynomial

/-- Rational squared norm in the unweighted DLMF triangle normalization. -/
theorem proriolTriangleMoment_sq_proriol (m k : ℕ) :
    proriolTriangleMoment ((proriol 0 0 0 (m+k) k)^2) =
      1 / (2*((m : ℝ)+k+1)*(2*k+1)) := by
  rw [← integral_sq_proriolMeasure_zero,
    integral_sq_proriolMeasure (by norm_num) (by norm_num) (by norm_num)]
  simp only [zero_add, add_zero, Nat.add_sub_cancel]
  rw [integral_sq_jacobi_zero_left (by have := Nat.cast_nonneg (α := ℝ) k; linarith : -1 < (2 : ℝ)*k+1),
    integral_sq_jacobi_zero_left (by norm_num : (-1 : ℝ) < 0)]
  rw [show (2 : ℝ)*k+1+1 = ((2*k+2 : ℕ) : ℝ) by push_cast; ring, rpow_natCast]
  norm_num only [rpow_ofNat, add_zero, zero_add, pow_one]
  rw [pow_add]
  have hp : (2 : ℝ)^(2*k) ≠ 0 := by positivity
  have hm : 2*(m : ℝ)+(2*k+1)+1 ≠ 0 := by positivity
  have hk : 2*(k : ℝ)+1 ≠ 0 := by positivity
  have hmk : (m : ℝ)+k+1 ≠ 0 := by positivity
  field_simp
  ring

end MvPolynomial
