/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.SeriesCalculus
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Regrouping absolutely convergent expansions
A family-independent coefficient pushforward, used to collect the output modes
of polynomial product formulas. Reference: ATAP, Chapter 3, product-to-sum.
-/

@[expose] public section
namespace Polynomial

/-- Coefficient data with a convergent sum in the specified output fibre. -/
def RegroupCoefficientInput {ι : Type*} (e : ι → ℕ) (k : ℕ) :=
  {c : ι → ℂ // Summable (fun i : {i // e i = k} ↦ c i)}

/-- A summable family gives admissible data on every fibre. -/
def RegroupCoefficientInput.ofSummable {ι : Type*} {c : ι → ℂ}
    (hc : Summable c) (e : ι → ℕ) (k : ℕ) : RegroupCoefficientInput e k :=
  ⟨c, hc.subtype _⟩

/-- Absolute summability supplies every fibre input (ATAP, Chapter 3). -/
def RegroupCoefficientInput.ofSummableNorm {ι : Type*} {c : ι → ℂ}
    (hc : Summable (fun i ↦ ‖c i‖)) (e : ι → ℕ) (k : ℕ) : RegroupCoefficientInput e k :=
  .ofSummable hc.of_norm e k

/-- A weighted norm majorant makes the contribution family summable. -/
theorem summable_mul_mode {ι : Type*} {c : ι → ℂ}
    (e : ι → ℕ) {P : ℕ → ℂ} {w : ℕ → ℝ}
    (hu : Summable (fun i ↦ ‖c i‖ * w (e i))) (hP : ∀ k, ‖P k‖ ≤ w k) :
    Summable (fun i ↦ c i * P (e i)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hu
  intro i
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hP (e i)) (norm_nonneg _)

/-- A weighted bound supplies convergent fibres of contributions, even at zero modes. -/
def RegroupCoefficientInput.ofWeightedBound {ι : Type*} {c : ι → ℂ}
    (e : ι → ℕ) {P : ℕ → ℂ} {w : ℕ → ℝ}
    (hu : Summable (fun i ↦ ‖c i‖ * w (e i))) (hP : ∀ k, ‖P k‖ ≤ w k)
    (k : ℕ) : RegroupCoefficientInput e k :=
  .ofSummable (summable_mul_mode e hu hP) e k

/-- Collect coefficients in one certified convergent output fibre. -/
noncomputable def regroupCoefficients {ι : Type*} {e : ι → ℕ} {k : ℕ}
    (c : RegroupCoefficientInput e k) : ℂ :=
  ∑' i : {i // e i = k}, c.val i

/-- The collected coefficient is the classical sum of its fibre. -/
theorem hasSum_regroupCoefficients {ι : Type*} {e : ι → ℕ} {k : ℕ}
    (c : RegroupCoefficientInput e k) :
    HasSum (fun i : {i // e i = k} ↦ c.val i) (regroupCoefficients c) :=
  c.property.hasSum

/-- Collecting modes preserves absolute summability. -/
theorem summable_norm_regroupCoefficients {ι : Type*} {c : ι → ℂ}
    (hc : Summable (fun i ↦ ‖c i‖)) (e : ι → ℕ) :
    Summable (fun k ↦ ‖regroupCoefficients (RegroupCoefficientInput.ofSummableNorm hc e k)‖) := by
  have h := hc.hasSum.tsum_fiberwise e
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ h.summable
  intro k
  exact norm_tsum_le_tsum_norm (hc.subtype (fun i ↦ e i = k))

/-- Regrouping does not increase the absolute coefficient mass. -/
theorem tsum_norm_regroupCoefficients_le {ι : Type*} {c : ι → ℂ}
    (hc : Summable (fun i ↦ ‖c i‖)) (e : ι → ℕ) :
    ∑' k, ‖regroupCoefficients (RegroupCoefficientInput.ofSummableNorm hc e k)‖ ≤
      ∑' i, ‖c i‖ := by
  have h := hc.hasSum.tsum_fiberwise e
  rw [← h.tsum_eq]
  exact (summable_norm_regroupCoefficients hc e).tsum_le_tsum
    (fun k ↦ norm_tsum_le_tsum_norm (hc.subtype (fun i ↦ e i = k))) h.summable

/-- Grouping contributions preserves the full weighted scope, including zero modes. -/
theorem hasSum_regrouped_series_of_weighted_bound {ι : Type*} {c : ι → ℂ}
    (e : ι → ℕ) {P : ℕ → ℂ} {w : ℕ → ℝ}
    (hu : Summable (fun i ↦ ‖c i‖ * w (e i))) (hP : ∀ k, ‖P k‖ ≤ w k) :
    HasSum (fun k ↦ regroupCoefficients (RegroupCoefficientInput.ofWeightedBound e hu hP k))
      (∑' i, c i * P (e i)) :=
  (summable_mul_mode e hu hP).hasSum.tsum_fiberwise e

/-- Convergent coefficient fibres permit factoring each output mode out of its sum. -/
theorem hasSum_regrouped_coefficients_of_weighted_bound {ι : Type*} {c : ι → ℂ}
    (e : ι → ℕ) {P : ℕ → ℂ} {w : ℕ → ℝ}
    (hu : Summable (fun i ↦ ‖c i‖ * w (e i))) (hP : ∀ k, ‖P k‖ ≤ w k)
    (hc : ∀ k, Summable (fun i : {i // e i = k} ↦ c i)) :
    HasSum (fun k ↦ regroupCoefficients ⟨c, hc k⟩ * P k) (∑' i, c i * P (e i)) := by
  have h := (summable_mul_mode e hu hP).hasSum.tsum_fiberwise e
  convert h using 1
  ext k
  change (∑' i : {i // e i = k}, c i) * P k = _
  rw [← tsum_mul_right]
  apply tsum_congr
  intro i
  rw [i.property]

/-- Absolutely summable coefficients can be grouped in any uniformly bounded family. -/
theorem hasSum_regrouped_series {ι : Type*} {c : ι → ℂ}
    (hc : Summable (fun i ↦ ‖c i‖)) (e : ι → ℕ) {P : ℕ → ℂ} {B : ℝ}
    (hP : ∀ k, ‖P k‖ ≤ B) :
    HasSum (fun k ↦ regroupCoefficients (RegroupCoefficientInput.ofSummableNorm hc e k) * P k)
      (∑' i, c i * P (e i)) := by
  exact hasSum_regrouped_coefficients_of_weighted_bound e (hc.mul_right B) hP
    (fun k ↦ hc.of_norm.subtype _)

/-- Products of approximants have an error controlled by their individual
errors and the sizes of the exact factors. -/
theorem norm_mul_sub_mul_le_errors {f g p q : ℂ} {A B ε η : ℝ}
    (hf : ‖f‖ ≤ A) (hq : ‖q‖ ≤ B) (he : ‖f - p‖ ≤ ε) (hh : ‖g - q‖ ≤ η) :
    ‖f * g - p * q‖ ≤ A * η + ε * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans hf
  have hε : 0 ≤ ε := (norm_nonneg _).trans he
  calc
    _ = ‖f * (g - q) + (f - p) * q‖ := by congr 1; ring
    _ ≤ ‖f * (g - q)‖ + ‖(f - p) * q‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul hf hh (norm_nonneg _) hA)
        (mul_le_mul he hq (norm_nonneg _) hε)

end Polynomial
