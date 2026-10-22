/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.DerivativeCoefficients
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Finite-smoothness bounds for Chebyshev coefficients

ATAP, Theorem 7.1, for a chain of absolutely continuous derivative
representatives whose last member has bounded variation. The last member may
have jumps; at smoothness zero the original function may have jumps.
-/

public section

namespace Polynomial.Chebyshev

open Real Set MeasureTheory

/-- Derivative-chain assumptions supply every classical coefficient input. -/
theorem coefficientInput_integrable_derivative_chain
    {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hvar : eVariationOn (F ν) (Icc (-1) 1) ≤ ENNReal.ofReal V) (n : ℕ) :
    Integrable (fun x ↦ F 0 x * (T ℝ n).eval x) classicalMeasureT := by
  apply coefficientInput_integrable_boundedVariation
  by_cases hν : ν = 0
  · subst ν
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  · simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
      (hAC 0 (Nat.pos_of_ne_zero hν)).boundedVariationOn

/-- The falling-factorial coefficient bound of ATAP, Theorem 7.1.
The derivative chain is interpreted almost everywhere, with no continuity
assumption on its last member. -/
theorem abs_coefficient_le_descFactorial_of_derivative_chain
    {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hV : 0 ≤ V)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hd : ∀ j < ν, ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt (F j) (F (j + 1) x) x)
    (hvar : eVariationOn (F ν) (Icc (-1) 1) ≤ ENNReal.ofReal V)
    {k : ℕ} (hk : ν + 1 ≤ k) :
    |(coefficient (n := k) ⟨(F 0), coefficientInput_integrable_derivative_chain hAC hvar _⟩)| ≤ 2 * V / (π * (k.descFactorial (ν + 1) : ℝ)) := by
  induction ν generalizing F k with
  | zero =>
    simpa using abs_coefficient_le_of_eVariationOn_le hV hvar (show k ≠ 0 by omega)
  | succ ν ih =>
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 2 := ⟨k - 2, by omega⟩
    have hAC' : ∀ j < ν, AbsolutelyContinuousOnInterval ((fun j ↦ F (j + 1)) j) (-1) 1 :=
      fun j hj ↦ hAC (j + 1) (by omega)
    have hd' : ∀ j < ν, ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 →
        HasDerivAt ((fun j ↦ F (j + 1)) j) ((fun j ↦ F (j + 1)) (j + 1) x) x :=
      fun j hj ↦ hd (j + 1) (by omega)
    have hlo := ih hAC' hd' hvar (k := n + 1) (by omega)
    have hhi := ih hAC' hd' hvar (k := n + 3) (by omega)
    have hBV : BoundedVariationOn (F 1) (Icc (-1) 1) := by
      by_cases hν : ν = 0
      · subst ν
        exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
      · simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
          (hAC 1 (by omega)).boundedVariationOn
    have hcos : BoundedVariationOn (fun θ ↦ F 1 (cos θ)) (Icc 0 π) :=
      ne_top_of_le_ne_top hBV (eVariationOn.comp_le_of_antitoneOn (F 1) cos antitoneOn_cos
        (fun θ _ ↦ ⟨neg_one_le_cos θ, cos_le_one θ⟩))
    have hint : IntervalIntegrable (fun θ ↦ F 1 (cos θ)) volume 0 π :=
      hcos.intervalIntegrable (by rw [uIcc_of_le pi_pos.le])
    rw [coefficient_eq_sub_derivative_coefficients (hAC 0 (by omega)) (hd 0 (by omega)) hint n,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (n + 2 : ℕ))]
    have hD : (0 : ℝ) < (n + 1).descFactorial (ν + 1) := by
      exact_mod_cast Nat.descFactorial_pos.mpr (show ν + 1 ≤ n + 1 by omega)
    have hmono : ((n + 1).descFactorial (ν + 1) : ℝ) ≤ (n + 3).descFactorial (ν + 1) := by
      exact_mod_cast Nat.descFactorial_le (ν + 1) (show n + 1 ≤ n + 3 by omega)
    have hhi' : |(coefficient (n := (n + 3)) ⟨(F 1), coefficientInput_integrable_boundedVariation hBV _⟩)| ≤
        2 * V / (π * ((n + 1).descFactorial (ν + 1) : ℝ)) :=
      hhi.trans (div_le_div_of_nonneg_left (by positivity) (mul_pos pi_pos hD)
        (mul_le_mul_of_nonneg_left hmono pi_pos.le))
    calc
      _ ≤ (2 * V / (π * ((n + 1).descFactorial (ν + 1) : ℝ)) +
          2 * V / (π * ((n + 1).descFactorial (ν + 1) : ℝ))) / (2 * (n + 2 : ℕ)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (abs_sub _ _).trans (add_le_add hlo hhi')
      _ = _ := by
        rw [Nat.succ_descFactorial_succ (n + 1) (ν + 1)]
        push_cast
        field_simp
        ring

/-- Comparing the falling-factorial and power expressions in ATAP, Theorem 7.1. -/
theorem descFactorial_coefficient_bound_le_pow {ν k : ℕ} {V : ℝ}
    (hV : 0 ≤ V) (hk : ν + 1 ≤ k) :
    2 * V / (π * (k.descFactorial (ν + 1) : ℝ)) ≤
      2 * V / (π * ((k : ℝ) - ν) ^ (ν + 1)) := by
  have hpow : ((k : ℝ) - ν) ^ (ν + 1) ≤ (k.descFactorial (ν + 1) : ℝ) := by
    have h := Nat.pow_sub_le_descFactorial k (ν + 1)
    rw [show k + 1 - (ν + 1) = k - ν by omega] at h
    have hc : ((k - ν : ℕ) : ℝ) ^ (ν + 1) ≤ (k.descFactorial (ν + 1) : ℝ) := by
      exact_mod_cast h
    simpa only [Nat.cast_sub (show ν ≤ k by omega)] using hc
  apply div_le_div_of_nonneg_left (by positivity) _ (mul_le_mul_of_nonneg_left hpow pi_pos.le)
  apply mul_pos pi_pos
  apply pow_pos
  exact sub_pos.mpr (by exact_mod_cast (show ν < k by omega))

/-- The simpler power bound following the falling-factorial estimate in
ATAP, Theorem 7.1. -/
theorem abs_coefficient_le_pow_of_derivative_chain
    {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hV : 0 ≤ V)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hd : ∀ j < ν, ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt (F j) (F (j + 1) x) x)
    (hvar : eVariationOn (F ν) (Icc (-1) 1) ≤ ENNReal.ofReal V)
    {k : ℕ} (hk : ν + 1 ≤ k) :
    |(coefficient (n := k) ⟨(F 0), coefficientInput_integrable_derivative_chain hAC hvar _⟩)| ≤ 2 * V / (π * ((k : ℝ) - ν) ^ (ν + 1)) :=
  (abs_coefficient_le_descFactorial_of_derivative_chain hV hAC hd hvar hk).trans
    (descFactorial_coefficient_bound_le_pow hV hk)

end Polynomial.Chebyshev
