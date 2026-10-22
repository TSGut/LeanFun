/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! # Integer angular modes on a full circle
Real sine/cosine orthogonality on (-pi,pi), including the constant cosine mode.
Reference: Fourier orthogonality and the angular factors in DLMF 18.37.1.
-/

public section
open MeasureTheory
namespace Real

/-- The integral of an integer cosine mode over a full circle. -/
theorem integral_cos_int_mode (k : ℤ) :
    ∫ θ in -π..π, cos (k*θ) = if k=0 then 2*π else 0 := by
  by_cases hk : k=0
  · simp [hk]
    ring
  · rw [ite_eq_right hk, intervalIntegral.integral_comp_mul_left _ (by exact_mod_cast hk),
      integral_cos]
    simp [mul_neg, sin_int_mul_pi]

/-- Every integer sine mode has zero integral over a full circle. -/
theorem integral_sin_int_mode (k : ℤ) :
    ∫ θ in -π..π, sin (k*θ) = 0 := by
  by_cases hk : k=0
  · simp [hk]
  · rw [intervalIntegral.integral_comp_mul_left _ (by exact_mod_cast hk), integral_sin]
    simp [mul_neg]

/-- Cosine modes are orthogonal, with squared norms pi and 2pi for the constant. -/
theorem integral_cos_mode_mul_cos_mode (m n : ℕ) :
    ∫ θ in -π..π, cos (m*θ)*cos (n*θ) =
      if m=n then (if m=0 then 2*π else π) else 0 := by
  have he (θ : ℝ) : cos (m*θ)*cos (n*θ) =
      (cos (((m : ℤ)-n : ℤ)*θ)+cos (((m : ℤ)+n : ℤ)*θ))/2 := by
    push_cast
    rw [sub_mul, add_mul, cos_sub, cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun θ : ℝ ↦ cos (((m : ℤ)-n : ℤ)*θ))).intervalIntegrable (-π) π)
    ((by fun_prop : Continuous (fun θ : ℝ ↦ cos (((m : ℤ)+n : ℤ)*θ))).intervalIntegrable (-π) π),
    integral_cos_int_mode, integral_cos_int_mode]
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0 <;> simp [hm]
  · have hd : (m : ℤ)-n ≠ 0 := by omega
    have hs : (m : ℤ)+n ≠ 0 := by omega
    simp [hmn, hd, hs]

/-- Sine modes are orthogonal; the zero mode has zero norm. -/
theorem integral_sin_mode_mul_sin_mode (m n : ℕ) :
    ∫ θ in -π..π, sin (m*θ)*sin (n*θ) = if m=n ∧ m≠0 then π else 0 := by
  have he (θ : ℝ) : sin (m*θ)*sin (n*θ) =
      (cos (((m : ℤ)-n : ℤ)*θ)-cos (((m : ℤ)+n : ℤ)*θ))/2 := by
    push_cast
    rw [sub_mul, add_mul, cos_sub, cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun θ : ℝ ↦ cos (((m : ℤ)-n : ℤ)*θ))).intervalIntegrable (-π) π)
    ((by fun_prop : Continuous (fun θ : ℝ ↦ cos (((m : ℤ)+n : ℤ)*θ))).intervalIntegrable (-π) π),
    integral_cos_int_mode, integral_cos_int_mode]
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0 <;> simp [hm]
  · have hd : (m : ℤ)-n ≠ 0 := by omega
    have hs : (m : ℤ)+n ≠ 0 := by omega
    simp [hmn, hd, hs]

/-- Sine and cosine modes are mutually orthogonal, including angular degree zero. -/
theorem integral_sin_mode_mul_cos_mode (m n : ℕ) :
    ∫ θ in -π..π, sin (m*θ)*cos (n*θ) = 0 := by
  have he (θ : ℝ) : sin (m*θ)*cos (n*θ) =
      (sin (((m : ℤ)+n : ℤ)*θ)+sin (((m : ℤ)-n : ℤ)*θ))/2 := by
    push_cast
    rw [sub_mul, add_mul, sin_add, sin_sub]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun θ : ℝ ↦ sin (((m : ℤ)+n : ℤ)*θ))).intervalIntegrable (-π) π)
    ((by fun_prop : Continuous (fun θ : ℝ ↦ sin (((m : ℤ)-n : ℤ)*θ))).intervalIntegrable (-π) π),
    integral_sin_int_mode, integral_sin_int_mode]
  simp

end Real
