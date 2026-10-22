/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Proriol.Basic
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Symmetry
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalDensity
import Mathlib.Topology.Algebra.Polynomial

/-! # Proriol marginal integration

Marginal integration on the DLMF triangle and its reflection to `0 ≤ y ≤ 1-x`.
The latter differs from the Gutleb–Olver convention by `(-1)^(n-k)`.
Reference: Gutleb–Olver, arXiv:1906.03907, Section 3.1; Gutleb's thesis,
Section 2.3, equation (2.7).
-/

@[expose] public noncomputable section
open MeasureTheory Set
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- Shifted Jacobi reflection, with the parameter swap (DLMF Table 18.6.1). -/
theorem eval_shiftedJacobi_one_sub (α β x : ℝ) (n : ℕ) :
    (shiftedJacobi α β n).eval (1-x) =
      (-1 : ℝ)^n * (shiftedJacobi β α n).eval x := by
  simp only [eval_shiftedJacobi]
  rw [show 2*(1-x)-1 = -(2*x-1) by ring, eval_jacobi_neg]

/-- The unweighted inner Jacobi modes have unit mass in degree zero and zero
mass otherwise (Gutleb's thesis, derivation of equation (2.7)). -/
theorem integral_shiftedJacobi_zero_zero (k : ℕ) :
    ∫ z in (0 : ℝ)..1, (shiftedJacobi 0 0 k).eval z = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [shiftedJacobi]
  · have h := integralInner_shiftedJacobi (0 : ℝ) 0 k 0
      (hi := (hasFiniteMoments_jacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _)
    have hz := integral_mul_jacobi_eq_zero (α := 0) (β := 0) (by norm_num)
      (by norm_num) hk
    simp only [integralInner] at h
    let g : IntegrableInput (unitJacobiMeasure 0 0) := ⟨fun x ↦ (shiftedJacobi 0 0 k).eval x * (shiftedJacobi 0 0 0).eval x, (hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _⟩
    have hg : Measurable g.val := by dsimp [g]; fun_prop
    have hd : (∫ x, g.val x ∂unitJacobiMeasure 0 0) = 2 *
        ∫ x in (0 : ℝ)..1, g.val x := by
      rw [integral_unitJacobiMeasure_subtype 0 0 g hg]
      simp only [unitJacobiWeight_apply, zero_add, Real.rpow_one, Real.rpow_zero,
        mul_one]
      rw [integral_const_mul, integral_subtype measurableSet_Ioo g.val,
        restrict_Ioo_eq_restrict_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    dsimp only [g] at hd
    rw [hz, hd] at h
    simp [shiftedJacobi, hk] at h ⊢
    linarith

end Polynomial
namespace MvPolynomial
open Polynomial

/-- The sign-normalized reflected DLMF polynomial is the separated Proriol
mode used by Gutleb–Olver. No division by the boundary factor is needed. -/
theorem eval_proriol_reflected_normalized_scaled (n k : ℕ) (x z : ℝ) :
    (-1 : ℝ)^(n-k) *
      eval (![1-x,(1-x)*z] : Fin 2 → ℝ) (proriol 0 0 0 n k) =
      (shiftedJacobi (2*k+1) 0 (n-k)).eval x * (1-x)^k *
        (shiftedJacobi 0 0 k).eval z := by
  rw [eval_proriol_scaled, eval_shiftedJacobi_one_sub]
  simp only [zero_add]
  calc
    _ = ((-1 : ℝ)^(n-k) * (-1)^(n-k)) *
        ((shiftedJacobi (2*k+1) 0 (n-k)).eval x * (1-x)^k *
          (shiftedJacobi 0 0 k).eval z) := by ring
    _ = _ := by rw [← mul_pow]; simp

/-- Integration along the inner coordinate removes every positive inner mode.
This formula also holds at the collapsed edge and for oriented real intervals. -/
theorem integral_proriol_inner (n k : ℕ) (x : ℝ) :
    ∫ y in (0 : ℝ)..x, eval (![x,y] : Fin 2 → ℝ) (proriol 0 0 0 n k) =
      if k = 0 then x * (shiftedJacobi 0 1 n).eval x else 0 := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1)
    (fun y ↦ eval (![x,y] : Fin 2 → ℝ) (proriol 0 0 0 n k)) x
  simp only [mul_zero, mul_one, smul_eq_mul, eval_proriol_scaled] at h
  rw [intervalIntegral.integral_const_mul, integral_shiftedJacobi_zero_zero] at h
  rw [← h]
  split_ifs with hk
  · subst k
    simp
  · simp

/-- Reflecting the DLMF triangle introduces the outer Jacobi parity factor.
The endpoint factor is retained explicitly, including at `x = 1`. -/
theorem integral_proriol_reflected (n k : ℕ) (x : ℝ) :
    ∫ y in (0 : ℝ)..(1-x), eval (![1-x,y] : Fin 2 → ℝ) (proriol 0 0 0 n k) =
      if k = 0 then (-1 : ℝ)^n * ((1-x) * (shiftedJacobi 1 0 n).eval x) else 0 := by
  rw [integral_proriol_inner]
  split_ifs
  · rw [eval_shiftedJacobi_one_sub]
    ring
  · rfl

/-- In the Gutleb–Olver normalization, the marginal is precisely the outer
shifted Jacobi mode times `1-x`; all positive inner degrees vanish. -/
theorem integral_proriol_reflected_normalized (n k : ℕ) (x : ℝ) :
    ∫ y in (0 : ℝ)..(1-x), (-1 : ℝ)^(n-k) *
      eval (![1-x,y] : Fin 2 → ℝ) (proriol 0 0 0 n k) =
      if k = 0 then (1-x) * (shiftedJacobi 1 0 n).eval x else 0 := by
  rw [intervalIntegral.integral_const_mul, integral_proriol_reflected]
  split_ifs with hk
  · subst k
    rw [Nat.sub_zero, ← mul_assoc, ← mul_pow]
    simp
  · simp

end MvPolynomial
