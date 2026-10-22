/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Lp.CoefficientShift
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # The first-order ultraspherical preconditioner and its boundary row
The diagonal is 1,1,1/2,1/3,... . Preconditioned endpoint evaluation is a
bounded functional on square-summable coefficients.
Reference: Olver--Townsend (2013), Section 4.1.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open Filter
open scoped Topology ENNReal

/-- First-order right-preconditioner diagonal, including the constant mode. -/
noncomputable def firstOrderDiagonal (n : ℕ) : ℂ :=
  ((if n = 0 then 1 else (n : ℝ)⁻¹ : ℝ) : ℂ)

@[simp] theorem firstOrderDiagonal_zero : firstOrderDiagonal 0 = 1 := by simp [firstOrderDiagonal]

@[simp] theorem firstOrderDiagonal_succ (n : ℕ) :
    firstOrderDiagonal (n + 1) = ((n + 1 : ℝ)⁻¹ : ℂ) := by simp [firstOrderDiagonal]

/-- The preconditioner diagonal is uniformly bounded by one. -/
theorem norm_firstOrderDiagonal_le (n : ℕ) : ‖firstOrderDiagonal n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · have h : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    simp only [firstOrderDiagonal, ite_eq_right hn, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact inv_le_one_of_one_le₀ h

/-- The diagonal vanishes at infinity. -/
theorem tendsto_firstOrderDiagonal : Tendsto firstOrderDiagonal atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ (((n : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_inv_atTop_nhds_zero_nat
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp [firstOrderDiagonal, Nat.ne_of_gt hn]

/-- The diagonal preconditioner as a bounded map on the existing lp space. -/
noncomputable def firstOrderPreconditioner :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  lp.coefficientDiagonal firstOrderDiagonal zero_le_one norm_firstOrderDiagonal_le

@[simp] theorem firstOrderPreconditioner_apply (x : lp (fun _ : ℕ ↦ ℂ) 2) (n : ℕ) :
    firstOrderPreconditioner x n = firstOrderDiagonal n * x n := rfl

/-- Diagonal decay makes the first-order preconditioner compact. -/
theorem isCompactOperator_firstOrderPreconditioner : IsCompactOperator firstOrderPreconditioner :=
  lp.isCompactOperator_coefficientDiagonal firstOrderDiagonal zero_le_one
    norm_firstOrderDiagonal_le tendsto_firstOrderDiagonal

/-- The coefficient vector representing endpoint evaluation after preconditioning. -/
noncomputable def firstOrderBoundaryVector : lp (fun _ : ℕ ↦ ℂ) 2 :=
  ⟨fun n ↦ (-1 : ℂ) ^ n * firstOrderDiagonal n, by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
    apply (summable_nat_add_iff 1).1
    have h := (summable_nat_add_iff 1).2
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ)))
    apply h.congr
    intro n
    have hn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by simpa using Complex.norm_natCast (n + 1)
    simp [firstOrderDiagonal, inv_pow, hn]⟩

/-- Bounded endpoint evaluation on preconditioned coefficient sequences. -/
noncomputable def firstOrderBoundary : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] ℂ :=
  innerSL ℂ firstOrderBoundaryVector

/-- The constant mode is normalized to one by the boundary functional. -/
theorem firstOrderBoundary_single_zero : firstOrderBoundary (lp.single 2 0 (1 : ℂ)) = 1 := by
  simp [firstOrderBoundary, innerSL_apply_apply, lp.inner_single_right,
    firstOrderBoundaryVector]

end Polynomial.Chebyshev
