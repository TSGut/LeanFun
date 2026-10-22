/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Function.ProductSeparation
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Separation test for quadratic disk modifications

After y = sqrt(1-x²) z, the density A+B x²+C y² becomes
A+B x²+C(1-x²)z². Its product-separation obstruction is C(A+B).
This does not assert a necessary condition for arbitrary finite Cholesky bandwidth.
Reference: Dunkl–Xu, §2.6.1; Gutleb–Olver–Slevinsky, measure modifications.
-/

public section
namespace Polynomial

/-- A quadratic disk density separates in Cartesian disk coordinates exactly
when it is an outer-only change or a multiple of (1-x²). -/
theorem quadraticDiskPullback_isProductSeparated_iff (A B C : ℝ) :
    Function.IsProductSeparated (fun x z : ℝ => A+B*x^2+C*(1-x^2)*z^2) ↔
      C = 0 ∨ A+B = 0 := by
  constructor
  · intro h
    have he := (Function.isProductSeparated_iff _).mp h 0 1 0 1
    have hz : C*(A+B) = 0 := by nlinarith [he]
    exact mul_eq_zero.mp hz
  · rintro (hC | hAB)
    · refine ⟨fun x => A+B*x^2, fun _ => 1, ?_⟩
      intro x z
      simp [hC]
    · refine ⟨fun x => 1-x^2, fun z => A+C*z^2, ?_⟩
      intro x z
      have hB : B = -A := by linarith
      rw [hB]
      ring

/-- The quadratic pullback's rectangle minor detects the same obstruction. -/
theorem quadraticDiskPullback_rectangle_minor (A B C : ℝ) :
    A*(A+B) - (A+C)*(A+B) = -C*(A+B) := by ring

/-- Positivity of a physical density does not imply product separation. -/
theorem not_isProductSeparated_one_add_disk_y_sq :
    ¬ Function.IsProductSeparated (fun x z : ℝ => 1+(1-x^2)*z^2) := by
  simpa using (show ¬ Function.IsProductSeparated
    (fun x z : ℝ => (1 : ℝ)+0*x^2+1*(1-x^2)*z^2) by
      rw [quadraticDiskPullback_isProductSeparated_iff]
      norm_num)

/-- Nonnegativity of a diagonal quadratic on the disk is decided at three vertices
of the triangle of squared coordinates. -/
theorem quadraticDisk_nonneg_iff (A B C : ℝ) :
    (∀ x y : ℝ, x^2+y^2 ≤ 1 → 0 ≤ A+B*x^2+C*y^2) ↔
      0 ≤ A ∧ 0 ≤ A+B ∧ 0 ≤ A+C := by
  constructor
  · intro h
    have h₀ := h 0 0 (by norm_num)
    have h₁ := h 1 0 (by norm_num)
    have h₂ := h 0 1 (by norm_num)
    simpa using And.intro h₀ (And.intro h₁ h₂)
  · rintro ⟨hA,hB,hC⟩ x y hxy
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hxy),
      mul_nonneg hB (sq_nonneg x), mul_nonneg hC (sq_nonneg y)]

end Polynomial
