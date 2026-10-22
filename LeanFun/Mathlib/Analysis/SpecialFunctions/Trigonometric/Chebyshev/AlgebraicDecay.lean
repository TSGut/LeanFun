/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.FiniteSmoothness
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.SeriesRepresentation
public import LeanFun.Mathlib.Analysis.PSeriesTail

/-!
# Algebraic truncation error for Chebyshev expansions

ATAP, Theorem 7.2, for an absolutely continuous derivative chain whose last
member has bounded variation. Series representation is proved before applying
the coefficient-tail estimate.
-/

public section

namespace Polynomial.Chebyshev

open Real Set MeasureTheory

/-- Positive smoothness and bounded variation of the last derivative imply
absolute summability of the Chebyshev coefficients (ATAP, Chapter 7). -/
theorem summable_abs_coefficient_of_derivative_chain
    {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ} (hν : 1 ≤ ν) (hV : 0 ≤ V)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hd : ∀ j < ν, ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt (F j) (F (j + 1) x) x)
    (hvar : eVariationOn (F ν) (Icc (-1) 1) ≤ ENNReal.ofReal V) :
    Summable (fun n ↦ |(coefficient (n := n) ⟨(F 0), coefficientInput_integrable_derivative_chain hAC hvar _⟩)|) := by
  have hp : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ (ν + 1)) :=
    summable_one_div_nat_pow.mpr (by omega)
  have hs := ((summable_nat_add_iff 1).2 hp).mul_left (2 * V / π)
  rw [← summable_nat_add_iff (ν + 1)]
  apply hs.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_abs]
  have hb := abs_coefficient_le_pow_of_derivative_chain hV hAC hd hvar
    (k := k + (ν + 1)) (by omega)
  have he : ((k + (ν + 1) : ℕ) : ℝ) - ν = (k + 1 : ℕ) := by push_cast; ring
  rw [he] at hb
  convert hb using 1
  ring

/-- The degree-`N` Chebyshev truncation has uniform algebraic error bounded by
`2V / (π ν (N - ν)^ν)` (ATAP, Theorem 7.2). -/
theorem abs_sub_sum_coefficient_le_of_derivative_chain
    {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ} (hν : 1 ≤ ν) (hV : 0 ≤ V)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hd : ∀ j < ν, ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt (F j) (F (j + 1) x) x)
    (hvar : eVariationOn (F ν) (Icc (-1) 1) ≤ ENNReal.ofReal V)
    {N : ℕ} (hN : ν < N) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |F 0 x - ∑ n ∈ Finset.range (N + 1), (coefficient (n := n) ⟨(F 0), coefficientInput_integrable_derivative_chain hAC hvar _⟩) * (T ℝ n).eval x| ≤
      2 * V / (π * ν * ((N : ℝ) - ν) ^ ν) := by
  have ha := summable_abs_coefficient_of_derivative_chain hν hV hAC hd hvar
  have hc : ContinuousOn (F 0) (Icc (-1) 1) := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
      (hAC 0 (by omega)).continuousOn
  apply (abs_sub_sum_le_tsum_tail ha hx (hasSum_coefficient_mul_eval_T hc ha hx) N).trans
  have hp : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ (ν + 1)) :=
    summable_one_div_nat_pow.mpr (by omega)
  have hmajor := ((summable_nat_add_iff (N - ν + 1)).2 hp).mul_left (2 * V / π)
  calc
    _ ≤ ∑' k : ℕ, (2 * V / π) * (1 / ((k + (N - ν + 1) : ℕ) : ℝ) ^ (ν + 1)) := by
      apply ((summable_nat_add_iff (N + 1)).2 ha).tsum_le_tsum _ hmajor
      intro k
      have hb := abs_coefficient_le_pow_of_derivative_chain hV hAC hd hvar
        (k := k + (N + 1)) (by omega)
      have he : ((k + (N + 1) : ℕ) : ℝ) - ν = (k + (N - ν + 1) : ℕ) := by
        push_cast [Nat.cast_sub hN.le]
        ring
      rw [he] at hb
      convert hb using 1
      ring
    _ = (2 * V / π) * ∑' k : ℕ, 1 / ((k + (N - ν + 1) : ℕ) : ℝ) ^ (ν + 1) :=
      tsum_mul_left
    _ ≤ (2 * V / π) * (1 / ((ν : ℝ) * ((N - ν : ℕ) : ℝ) ^ ν)) :=
      mul_le_mul_of_nonneg_left (tsum_one_div_nat_add_pow_le hν (by omega)) (by positivity)
    _ = _ := by
      rw [Nat.cast_sub hN.le]
      ring

/-- The smooth truncation error is bounded above on the closed interval
(ATAP, Theorem 7.2), so its real supremum is a genuine least upper bound. -/
theorem bddAbove_abs_sub_sum_coefficient_of_derivative_chain
    {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ} (hν : 1 ≤ ν) (hV : 0 ≤ V)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hd : ∀ j < ν, ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt (F j) (F (j + 1) x) x)
    (hvar : eVariationOn (F ν) (Icc (-1) 1) ≤ ENNReal.ofReal V)
    {N : ℕ} (hN : ν < N) :
    BddAbove (Set.range (fun x : Icc (-1 : ℝ) 1 ↦
      |F 0 x - ∑ n ∈ Finset.range (N + 1), (coefficient (n := n) ⟨(F 0), coefficientInput_integrable_derivative_chain hAC hvar _⟩) * (T ℝ n).eval (x : ℝ)|)) := by
  refine ⟨2 * V / (π * ν * ((N : ℝ) - ν) ^ ν), ?_⟩
  rintro y ⟨x, rfl⟩
  exact abs_sub_sum_coefficient_le_of_derivative_chain hν hV hAC hd hvar hN x.property

/-- The supremum form of the uniform truncation bound (ATAP, Theorem 7.2).

The pointwise theorem `abs_sub_sum_coefficient_le_of_derivative_chain` also
establishes boundedness of the error family, so this real supremum is its genuine
least upper bound. Use that theorem directly for pointwise error estimates. -/
theorem sup_abs_sub_sum_coefficient_le_of_derivative_chain
    {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ} (hν : 1 ≤ ν) (hV : 0 ≤ V)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hd : ∀ j < ν, ∀ᵐ x ∂volume, x ∈ Icc (-1) 1 → HasDerivAt (F j) (F (j + 1) x) x)
    (hvar : eVariationOn (F ν) (Icc (-1) 1) ≤ ENNReal.ofReal V)
    {N : ℕ} (hN : ν < N) :
    (⨆ x : Icc (-1 : ℝ) 1,
      |F 0 x - ∑ n ∈ Finset.range (N + 1), (coefficient (n := n) ⟨(F 0), coefficientInput_integrable_derivative_chain hAC hvar _⟩) * (T ℝ n).eval (x : ℝ)|) ≤
      2 * V / (π * ν * ((N : ℝ) - ν) ^ ν) := by
  have : Nonempty (Icc (-1 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
  exact ciSup_le fun x ↦ abs_sub_sum_coefficient_le_of_derivative_chain hν hV hAC hd hvar hN x.property

end Polynomial.Chebyshev
