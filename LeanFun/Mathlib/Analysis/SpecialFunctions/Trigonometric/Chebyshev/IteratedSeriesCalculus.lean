/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.IteratedSeriesCalculus
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.SeriesDifferentiation

/-! # Higher Chebyshev derivatives and the ultraspherical ladder
Convergence is inherited from the general polynomial theorem; the coefficient
formula reuses the existing finite bridge. Reference: ATAP, Chapter 21;
Olver--Townsend (2013), Section 3.
-/

@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open Complex Set Filter
open scoped Topology

/-- Each higher differentiated series sums to its classical derivative value. -/
theorem hasSum_iterated_derivative_complexChebyshevSeries {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (k : ℕ)
    (z : bernsteinEllipse ⟨ρ, hρ⟩) :
    HasSum (fun n ↦ a n * (derivative^[k] (T ℂ n)).eval z.val)
      (iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha k) z) := by
  rw [iteratedDeriv_complexChebyshevSeries_eq]
  obtain ⟨r, hr, hrρ, hzr⟩ := exists_smaller_bernsteinEllipse hρ z.property
  exact hasSum_iterated_derivative_series (P := fun n ↦ T ℂ n) (a := a)
    (isOpen_bernsteinEllipse ⟨r, hr⟩)
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ r / ρ)
      ((div_lt_one (by linarith : 0 < ρ)).2 hrρ)).mul_left C)
    (norm_chebyshev_term_le_geometric hρ hr ha) k hzr
/-- Every positive derivative order enters its corresponding ultraspherical basis. -/
theorem hasSum_gegenbauer_iterated_derivative_series {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (k : ℕ) (z : bernsteinEllipse ⟨ρ, hρ⟩) :
    HasSum (fun n ↦ a (n + k + 1) * ((2 : ℂ) ^ k * k.factorial * (n + k + 1)) *
      (gegenbauer (k + 1 : ℂ) n).eval z.val)
      (iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha (k + 1)) z) := by
  have ht := (hasSum_nat_add_iff' (k + 1)).2
    (hasSum_iterated_derivative_complexChebyshevSeries hρ ha (k + 1) z)
  have hz0 : ∑ n ∈ Finset.range (k + 1),
      a n * (derivative^[k + 1] (T ℂ n)).eval z.val = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [iterate_derivative_chebyshev_T_eq_zero ℂ (Finset.mem_range.mp hn), eval_zero, mul_zero]
  rw [hz0, sub_zero] at ht
  simpa only [← Nat.add_assoc, iterate_derivative_chebyshev_T, eval_mul, eval_C,
    mul_assoc] using ht

/-- All-order truncation bounds for the classical derivative values. -/
theorem norm_iterated_derivative_complexChebyshevSeries_sub_sum_le {a : ℕ → ℂ}
    {C ρ r δ : ℝ} (hρ : 1 < ρ) (hr : 1 < r) (hrρ : r < ρ)
    (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (k : ℕ) (z : bernsteinEllipse ⟨ρ, hρ⟩)
    (hz : z.val ∈ bernsteinEllipse ⟨r, hr⟩) (hδ : 0 < δ)
    (hball : Metric.sphere z.val δ ⊆ bernsteinEllipse ⟨r, hr⟩) (N : ℕ) :
    ‖iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha k) z -
      ∑ n ∈ Finset.range N, a n * (derivative^[k] (T ℂ n)).eval z.val‖ ≤
      k.factorial * (C * (r / ρ) ^ N / (1 - r / ρ)) / δ ^ k := by
  rw [iteratedDeriv_complexChebyshevSeries_eq]
  have hq0 : 0 ≤ r / ρ := by positivity
  have hq1 : r / ρ < 1 := (div_lt_one (by linarith : 0 < ρ)).2 hrρ
  have h := norm_iterated_derivative_series_sub_sum_le (P := fun n ↦ T ℂ n) (a := a)
    (isOpen_bernsteinEllipse ⟨r, hr⟩) ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
    (norm_chebyshev_term_le_geometric hρ hr ha) k hz hδ hball N
  simpa only [tsum_geometric_majorant_tail hq0 hq1 N] using h
/-- One Cauchy radius works uniformly on each compact subset, for all orders. -/
theorem exists_uniform_iterated_derivative_series_bound {a : ℕ → ℂ} {C ρ r : ℝ}
    (hρ : 1 < ρ) (hr : 1 < r) (hrρ : r < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    {K : Set ℂ} (hK : IsCompact K) (hKr : K ⊆ bernsteinEllipse ⟨r, hr⟩) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : bernsteinEllipse ⟨ρ, hρ⟩, z.val ∈ K → ∀ k N : ℕ,
      ‖iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha k) z -
        ∑ n ∈ Finset.range N, a n * (derivative^[k] (T ℂ n)).eval z.val‖ ≤
        k.factorial * (C * (r / ρ) ^ N / (1 - r / ρ)) / δ ^ k := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (isOpen_bernsteinEllipse ⟨r, hr⟩) hKr
  refine ⟨δ, hδ, fun z hz k N ↦ ?_⟩
  apply norm_iterated_derivative_complexChebyshevSeries_sub_sum_le hρ hr hrρ ha k z (hKr hz) hδ
  exact Metric.sphere_subset_closedBall.trans ((Metric.closedBall_subset_cthickening hz δ).trans hsub)

end Polynomial.Chebyshev
