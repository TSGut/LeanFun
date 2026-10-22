/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Connection
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Real.Basic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Orthogonality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Two-term symmetric Jacobi conversions

Raising both equal parameters leaves only equal-parity degrees. Multiplication
by `1-x²` gives the reverse two-term relation. These are the one-dimensional
identities needed by Cartesian disk parameter raising.

Reference: DLMF 18.9; Dunkl–Xu, disk orthogonal polynomials.
-/

@[expose] public section
namespace Polynomial

private theorem smul_of_cleared_two_term (p q r : ℝ[X]) (d a b : ℝ)
    (hd : d ≠ 0) (h : C d * p = C a * q + C b * r) :
    p = (d⁻¹ * a) • q + (d⁻¹ * b) • r := by
  apply mul_left_cancel₀ (C_ne_zero.mpr hd)
  rw [h]
  simp only [smul_eq_C_mul, mul_add, ← mul_assoc, ← map_mul]
  simp [hd]

/-- The index-dependent classical denominator domain for symmetric RaiseA coefficients. -/
structure JacobiSymmetricRaiseAInput (β : ℝ) (n : ℕ) : Prop where
  nonzero : (match n with
      | 0 => (1 : ℝ)
      | 1 => β + 2
      | m+2 => (2*(m : ℝ)+2*β+5)*(2*m+2*β+6)*(2*m+2*β+4)) ≠ 0

/-- The full orthogonality range lies in this classical coefficient domain. -/
theorem JacobiSymmetricRaiseAInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    JacobiSymmetricRaiseAInput β n := by
  constructor
  rcases n with _ | _ | n
  · norm_num
  · dsimp; linarith
  · dsimp
    have hn := Nat.cast_nonneg (α := ℝ) n
    exact mul_ne_zero (mul_ne_zero (ne_of_gt (by linarith))
      (ne_of_gt (by linarith))) (ne_of_gt (by linarith))

/-- The index-dependent classical denominator domain for symmetric RaiseB coefficients. -/
structure JacobiSymmetricRaiseBInput (β : ℝ) (n : ℕ) : Prop where
  nonzero : (match n with
      | 0 => (1 : ℝ)
      | 1 => 1
      | m+2 => (2*(m : ℝ)+2*β+5)*(2*m+2*β+6)*(2*m+2*β+4)) ≠ 0

/-- The full orthogonality range lies in this classical coefficient domain. -/
theorem JacobiSymmetricRaiseBInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    JacobiSymmetricRaiseBInput β n := by
  constructor
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · dsimp
    have hn := Nat.cast_nonneg (α := ℝ) n
    exact mul_ne_zero (mul_ne_zero (ne_of_gt (by linarith))
      (ne_of_gt (by linarith))) (ne_of_gt (by linarith))

/-- The index-dependent classical denominator domain for symmetric Lower coefficients. -/
structure JacobiSymmetricLowerInput (β : ℝ) (n : ℕ) : Prop where
  nonzero : (2*(n : ℝ)+2*β+2)*((n : ℝ)+2*β+2)*(2*n+2*β+3)*(2*n+2*β+4) ≠ 0

/-- The full orthogonality range lies in this classical coefficient domain. -/
theorem JacobiSymmetricLowerInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    JacobiSymmetricLowerInput β n := by
  constructor
  have hn := Nat.cast_nonneg (α := ℝ) n
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (by linarith))
    (ne_of_gt (by linarith))) (ne_of_gt (by linarith))) (ne_of_gt (by linarith))

/-- The unchanged-degree coefficient for symmetric raising, with the initial
cases separated to avoid removable singularities (DLMF 18.9). -/
noncomputable def jacobiSymmetricRaiseA (β : ℝ) (n : ℕ) (_d : JacobiSymmetricRaiseAInput β n := by
      exact Polynomial.JacobiSymmetricRaiseAInput.of_neg_one_lt (by linarith) _) : ℝ :=
  match n with
  | 0 => 1
  | 1 => (β + 1) / (β + 2)
  | n + 2 =>
    ((2 * n + 2 * β + 5) * (2 * n + 2 * β + 6) * (2 * n + 2 * β + 4))⁻¹ *
      ((2 * n + 2 * β + 4) * (n + 2 * β + 3) * (n + 2 * β + 4))

/-- Evaluation on the full classical coefficient domain. -/
theorem jacobiSymmetricRaiseA_apply (β : ℝ) (n : ℕ) (input : JacobiSymmetricRaiseAInput β n) :
    jacobiSymmetricRaiseA β n input =
  match n with
  | 0 => 1
  | 1 => (β + 1) / (β + 2)
  | n + 2 =>
    ((2 * n + 2 * β + 5) * (2 * n + 2 * β + 6) * (2 * n + 2 * β + 4))⁻¹ *
      ((2 * n + 2 * β + 4) * (n + 2 * β + 3) * (n + 2 * β + 4)) := rfl

/-- The degree-minus-two coefficient; it is zero in degrees zero and one. -/
noncomputable def jacobiSymmetricRaiseB (β : ℝ) (n : ℕ) (_d : JacobiSymmetricRaiseBInput β n := by
      exact Polynomial.JacobiSymmetricRaiseBInput.of_neg_one_lt (by linarith) _) : ℝ :=
  match n with
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    ((2 * n + 2 * β + 5) * (2 * n + 2 * β + 6) * (2 * n + 2 * β + 4))⁻¹ *
      (-((2 * n + 2 * β + 6) * (n + β + 2) ^ 2))

/-- Evaluation on the full classical coefficient domain. -/
theorem jacobiSymmetricRaiseB_apply (β : ℝ) (n : ℕ) (input : JacobiSymmetricRaiseBInput β n) :
    jacobiSymmetricRaiseB β n input =
  match n with
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    ((2 * n + 2 * β + 5) * (2 * n + 2 * β + 6) * (2 * n + 2 * β + 4))⁻¹ *
      (-((2 * n + 2 * β + 6) * (n + β + 2) ^ 2)) := rfl

/-- The degree-plus-two coefficient for multiplication by the boundary polynomial. -/
noncomputable def jacobiSymmetricLowerA (β : ℝ) (n : ℕ)
    (_d : JacobiSymmetricLowerInput β n := by exact Polynomial.JacobiSymmetricLowerInput.of_neg_one_lt (by linarith) _) : ℝ :=
  ((2 * n + 2 * β + 2) * (n + 2 * β + 2) *
    (2 * n + 2 * β + 3) * (2 * n + 2 * β + 4))⁻¹ *
      (-4 * (n + 1) * (n + 2) * (n + 2 * β + 2) * (2 * n + 2 * β + 2))

/-- Evaluation on the full classical coefficient domain. -/
theorem jacobiSymmetricLowerA_apply (β : ℝ) (n : ℕ) (input : JacobiSymmetricLowerInput β n) :
    jacobiSymmetricLowerA β n input =
  ((2 * n + 2 * β + 2) * (n + 2 * β + 2) *
    (2 * n + 2 * β + 3) * (2 * n + 2 * β + 4))⁻¹ *
      (-4 * (n + 1) * (n + 2) * (n + 2 * β + 2) * (2 * n + 2 * β + 2)) := rfl

/-- The unchanged-degree coefficient for multiplication by the boundary polynomial. -/
noncomputable def jacobiSymmetricLowerB (β : ℝ) (n : ℕ)
    (_d : JacobiSymmetricLowerInput β n := by exact Polynomial.JacobiSymmetricLowerInput.of_neg_one_lt (by linarith) _) : ℝ :=
  ((2 * n + 2 * β + 2) * (n + 2 * β + 2) *
    (2 * n + 2 * β + 3) * (2 * n + 2 * β + 4))⁻¹ *
      (4 * (n + β + 1) ^ 2 * (2 * n + 2 * β + 4) * (n + 2 * β + 2))

/-- Evaluation on the full classical coefficient domain. -/
theorem jacobiSymmetricLowerB_apply (β : ℝ) (n : ℕ) (input : JacobiSymmetricLowerInput β n) :
    jacobiSymmetricLowerB β n input =
  ((2 * n + 2 * β + 2) * (n + 2 * β + 2) *
    (2 * n + 2 * β + 3) * (2 * n + 2 * β + 4))⁻¹ *
      (4 * (n + β + 1) ^ 2 * (2 * n + 2 * β + 4) * (n + 2 * β + 2)) := rfl

/-- Simultaneously raising symmetric parameters only uses degrees `n+2` and `n`.
The full range `β > -1`, including `β = -1/2`, is retained. -/
theorem jacobi_symmetric_raise {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    jacobi β β (n + 2) =
      jacobiSymmetricRaiseA β (n + 2) • jacobi (β + 1) (β + 1) (n + 2) +
      jacobiSymmetricRaiseB β (n + 2) • jacobi (β + 1) (β + 1) n := by
  let d₀ := 2 * (n : ℝ) + 2 * β + 5
  let d₁ := 2 * (n : ℝ) + 2 * β + 6
  let d₂ := 2 * (n : ℝ) + 2 * β + 4
  have hd : d₀ * d₁ * d₂ ≠ 0 := by
    dsimp [d₀, d₁, d₂]
    have hn := Nat.cast_nonneg (α := ℝ) n
    exact mul_ne_zero (mul_ne_zero (ne_of_gt (by linarith))
      (ne_of_gt (by linarith))) (ne_of_gt (by linarith))
  apply smul_of_cleared_two_term _ _ _ (d₀ * d₁ * d₂)
    (d₂ * (n + 2 * β + 3) * (n + 2 * β + 4))
    (-(d₁ * (n + β + 2) ^ 2)) hd
  have h₀ := jacobi_raise_alpha β β (n + 1)
  have h₁ := jacobi_raise_beta (β + 1) β (n + 1)
  have h₂ := jacobi_raise_beta (β + 1) β n
  dsimp [d₀, d₁, d₂]
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_pow,
    map_natCast, map_ofNat, map_one, map_neg] at h₀ h₁ h₂ ⊢
  linear_combination
    (2 * n + 2 * C β + 6) * (2 * n + 2 * C β + 4) * h₀ +
    (2 * n + 2 * C β + 4) * (n + 2 * C β + 3) * h₁ -
    (2 * n + 2 * C β + 6) * (n + C β + 2) * h₂

/-- The reverse symmetric connection after multiplication by the quadratic
boundary polynomial also uses only two degrees. -/
theorem jacobi_symmetric_weight_lower {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    (1 - X ^ 2) * jacobi (β + 1) (β + 1) n =
      jacobiSymmetricLowerA β n • jacobi β β (n + 2) +
      jacobiSymmetricLowerB β n • jacobi β β n := by
  let d₀ := 2 * (n : ℝ) + 2 * β + 2
  let d₁ := (n : ℝ) + 2 * β + 2
  let d₂ := 2 * (n : ℝ) + 2 * β + 3
  let d₃ := 2 * (n : ℝ) + 2 * β + 4
  have hd : d₀ * d₁ * d₂ * d₃ ≠ 0 := by
    dsimp [d₀, d₁, d₂, d₃]
    have hn := Nat.cast_nonneg (α := ℝ) n
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (by linarith))
      (ne_of_gt (by linarith))) (ne_of_gt (by linarith))) (ne_of_gt (by linarith))
  apply smul_of_cleared_two_term _ _ _ (d₀ * d₁ * d₂ * d₃)
    (-4 * (n + 1) * (n + 2) * d₁ * d₀)
    (4 * (n + β + 1) ^ 2 * d₃ * d₁) hd
  have hl := jacobi_derivative_lowering β β n
  have hr := jacobi_recurrence β β n
  rw [derivative_jacobi_succ] at hl
  dsimp [d₀, d₁, d₂, d₃]
  simp only [ map_add, map_mul, map_pow,
    map_natCast, map_ofNat, map_one, map_neg, sub_self, map_zero, zero_sub] at hl hr ⊢
  norm_num at hl
  have hhalf : (2 : ℝ[X]) * C (1 / 2 : ℝ) = 1 := by
    have hh := congrArg (C : ℝ →+* ℝ[X]) (show (2 : ℝ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using hh
  linear_combination
    2 * (2 * n + 2 * C β + 3) * (2 * n + 2 * C β + 4) * hl +
    2 * (n + 1) * hr -
    ((2 * n + 2 * C β + 2) * (n + 2 * C β + 2) *
      (2 * n + 2 * C β + 3) * (2 * n + 2 * C β + 4) *
      (1 - X ^ 2) * jacobi (β + 1) (β + 1) n) * hhalf

/-- Existential wrapper for the explicit symmetric raising coefficients. -/
theorem exists_jacobi_symmetric_raise {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    ∃ a b : ℝ, jacobi β β (n + 2) =
      a • jacobi (β + 1) (β + 1) (n + 2) + b • jacobi (β + 1) (β + 1) n :=
  ⟨_, _, jacobi_symmetric_raise hβ n⟩

/-- Existential wrapper for the explicit boundary-weight connection. -/
theorem exists_jacobi_symmetric_weight_lower {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    ∃ a b : ℝ, (1 - X ^ 2) * jacobi (β + 1) (β + 1) n =
      a • jacobi β β (n + 2) + b • jacobi β β n :=
  ⟨_, _, jacobi_symmetric_weight_lower hβ n⟩

/-- The two-term raising relation including both initial degrees; the lower
coefficient vanishes when its intended degree would be negative. -/
theorem jacobi_symmetric_raise_all {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    jacobi β β n =
      jacobiSymmetricRaiseA β n • jacobi (β + 1) (β + 1) n +
      jacobiSymmetricRaiseB β n • jacobi (β + 1) (β + 1) (n - 2) ∧
      (n < 2 → jacobiSymmetricRaiseB β n = 0) := by
  rcases n with _ | _ | n
  · simp [jacobiSymmetricRaiseA, jacobiSymmetricRaiseB]
  · refine ⟨?_, by simp [jacobiSymmetricRaiseB]⟩
    simp only [jacobiSymmetricRaiseA, jacobiSymmetricRaiseB]
    have hb : β + 2 ≠ 0 := by linarith
    have he (t : ℝ) : jacobi t t 1 = C (t + 1) * X := by
      rw [jacobi_one]
      have ht : (algebraMap ℚ ℝ) (1 / 2) * (t + t + 2) = t + 1 := by
        norm_num
        ring
      rw [ht]
      ring
    change jacobi β β 1 = _
    rw [zero_smul, add_zero, he, he, smul_eq_C_mul, ← mul_assoc, ← map_mul]
    congr 1
    congr 1
    field_simp
    ring
  · exact ⟨by simpa [Nat.succ_eq_add_one, add_assoc] using jacobi_symmetric_raise hβ n,
      by omega⟩

/-- Existential wrapper for the all-degree symmetric raising formula. -/
theorem exists_jacobi_symmetric_raise_all {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    ∃ a b : ℝ, jacobi β β n =
      a • jacobi (β + 1) (β + 1) n + b • jacobi (β + 1) (β + 1) (n - 2) ∧
      (n < 2 → b = 0) :=
  ⟨_, _, jacobi_symmetric_raise_all hβ n⟩

/-- The coefficient of the unchanged degree in symmetric parameter raising is positive. -/
theorem exists_jacobi_symmetric_raise_all_pos {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    ∃ a b : ℝ, 0 < a ∧ jacobi β β n =
      a • jacobi (β + 1) (β + 1) n + b • jacobi (β + 1) (β + 1) (n - 2) ∧
      (n < 2 → b = 0) := by
  obtain ⟨a, b, h, hb⟩ := exists_jacobi_symmetric_raise_all hβ n
  refine ⟨a, b, ?_, h, hb⟩
  have hc := congrArg (fun p : ℝ[X] => p.coeff n) h
  simp only [coeff_add, coeff_smul, smul_eq_mul] at hc
  have hz : b * (jacobi (β + 1) (β + 1) (n - 2)).coeff n = 0 := by
    by_cases hn : n < 2
    · rw [hb hn, zero_mul]
    · rw [coeff_eq_zero_of_natDegree_lt
        ((natDegree_jacobi_le _ _ _).trans_lt (by omega : n - 2 < n)), mul_zero]
  rw [hz, add_zero] at hc
  have hp := coeff_jacobi_self_pos
    (show -1 < β + 1 by linarith) (show -1 < β + 1 by linarith) n
  have hp' := coeff_jacobi_self_pos hβ hβ n
  rw [hc] at hp'
  exact (mul_pos_iff_of_pos_right hp).mp hp'

end Polynomial
