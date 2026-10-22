/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.SeriesCalculus
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.AnalyticConverse
public import LeanFun.Mathlib.RingTheory.Polynomial.Chebyshev.Gegenbauer

public import LeanFun.Mathlib.Analysis.Calculus.IteratedDeriv.OpenDomain

/-! # Differentiating analytic Chebyshev series
The convergence argument is family-independent; the ultraspherical entry uses
the existing polynomial bridge. Reference: ATAP, Chapter 21; DLMF 18.9.21.
-/

@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open Complex Set

/-- A normally convergent polynomial expansion supplies actual series points. -/
def ComplexChebyshevSeriesPoint.ofNormal {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (T ℂ n).eval z‖ ≤ u n) (z : U) :
    ComplexChebyshevSeriesPoint a :=
  .ofSummable ((Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ hb n z.val z.property) hu).of_norm)

@[simp] theorem ComplexChebyshevSeriesPoint.ofNormal_val {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (T ℂ n).eval z‖ ≤ u n) (z : U) :
    (ComplexChebyshevSeriesPoint.ofNormal hu hb z).val = z.val := rfl

/-- Normal convergence gives analyticity on the actual open domain. -/
theorem analyticOnOpen_complexChebyshevSeries_of_normal {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U : TopologicalSpace.Opens ℂ} (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (T ℂ n).eval z‖ ≤ u n) :
    AnalyticOnOpen U (fun z ↦ complexChebyshevSeries a (.ofNormal hu hb z)) := by
  apply (analyticOnOpen_iff _ _ (fun z ↦ ∑' n, a n * (T ℂ n).eval z) ?_).2
  · exact (differentiableOn_tsum_of_summable_norm hu
      (fun n ↦ ((T ℂ n).differentiable.const_mul (a n)).differentiableOn)
      U.isOpen hb).analyticOnNhd U.isOpen
  · intro z
    have hs : Summable (fun n : ℕ ↦ a n * (T ℂ n).eval z.val) :=
      (Summable.of_nonneg_of_le (fun n : ℕ ↦ norm_nonneg (a n * (T ℂ n).eval z.val))
        (fun n ↦ hb n z.val z.property) hu).of_norm
    exact (complexChebyshevSeries_eq_tsum (ComplexChebyshevSeriesPoint.ofNormal hu hb z)
      (by simpa only [ComplexChebyshevSeriesPoint.ofNormal_val] using hs)).symm

/-- Geometric data supply an actual derivative input, at every finite order. -/
def complexChebyshevSeriesDerivInput {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (k : ℕ) :
    IteratedDerivInput ⟨bernsteinEllipse ⟨ρ, hρ⟩, isOpen_bernsteinEllipse ⟨ρ, hρ⟩⟩ k :=
  .ofAnalytic _ (analyticOnOpen_complexChebyshevSeries hρ ha) k

/-- The geometric derivative input carries the actual chain of the series. -/
theorem complexChebyshevSeriesDerivInput_spec {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (k : ℕ) :
    HasIteratedDerivOnOpen ⟨bernsteinEllipse ⟨ρ, hρ⟩, isOpen_bernsteinEllipse ⟨ρ, hρ⟩⟩ k
      (fun z ↦ complexChebyshevSeries a (.ofGeometric hρ ha z))
      (iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha k)) :=
  iteratedDerivOnOpen_spec (complexChebyshevSeriesDerivInput hρ ha k)

/-- Internal bridge valid only on the ellipse of actual analyticity. -/
theorem iteratedDeriv_complexChebyshevSeries_eq {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (k : ℕ)
    (z : bernsteinEllipse ⟨ρ, hρ⟩) :
    iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha k) z =
      iteratedDeriv k (fun w ↦ ∑' n, a n * (T ℂ n).eval w) z.val := by
  have h := iteratedDerivOnOpen_eq_iteratedDeriv
    (complexChebyshevSeriesDerivInput hρ ha k)
    (fun w ↦ ∑' n, a n * (T ℂ n).eval w)
    (analyticOnNhd_chebyshev_tsum hρ ha) (fun w ↦ ?_)
  · exact congrFun h z
  · have hw : w.val ∈ bernsteinEllipse ⟨ρ, hρ⟩ := w.property
    exact (complexChebyshevSeries_eq_tsum
      (ComplexChebyshevSeriesPoint.ofGeometric hρ ha ⟨w.val, hw⟩)
      (by simpa only [ComplexChebyshevSeriesPoint.ofGeometric_val] using
        summable_chebyshevSeries_of_geometric hρ ha (z := w.val) hw)).symm

end Polynomial.Chebyshev
@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open Complex Set Filter
open scoped Topology

/-- Geometric coefficients give a uniform majorant on each smaller ellipse. -/
theorem norm_chebyshev_term_le_geometric {a : ℕ → ℂ} {C ρ r : ℝ} (hρ : 1 < ρ) (hr : 1 < r)
    (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (n : ℕ) (z : ℂ) (hz : z ∈ bernsteinEllipse ⟨r, hr⟩) :
    ‖a n * (T ℂ n).eval z‖ ≤ C * (r / ρ) ^ n := by
  have hC : 0 ≤ C := (norm_nonneg (a 0)).trans (by simpa using ha 0)
  rw [norm_mul]
  calc
    _ ≤ (C / ρ ^ n) * r ^ n := mul_le_mul (ha n)
      (norm_eval_T_le_on_bernsteinEllipse hr hz n) (norm_nonneg _) (by positivity)
    _ = _ := by rw [div_pow]; ring

/-- The differentiated terms sum to the actual classical derivative. -/
theorem hasSum_derivative_complexChebyshevSeries {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    (z : bernsteinEllipse ⟨ρ, hρ⟩) :
    HasSum (fun n ↦ a n * (T ℂ n).derivative.eval z.val)
      (iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha 1) z) := by
  rw [iteratedDeriv_complexChebyshevSeries_eq, iteratedDeriv_one]
  obtain ⟨r, hr, hrρ, hzr⟩ := exists_smaller_bernsteinEllipse hρ z.property
  exact hasSum_derivative_series (isOpen_bernsteinEllipse ⟨r, hr⟩)
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ r / ρ)
      ((div_lt_one (by linarith : 0 < ρ)).2 hrρ)).mul_left C)
    (norm_chebyshev_term_le_geometric hρ hr ha) hzr

/-- The first derivative enters the C^(1) basis, with the constant mode removed. -/
theorem hasSum_gegenbauer_derivative_complexChebyshevSeries {a : ℕ → ℂ} {C ρ : ℝ}
    (hρ : 1 < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n) (z : bernsteinEllipse ⟨ρ, hρ⟩) :
    HasSum (fun n ↦ a (n + 1) * (n + 1 : ℂ) * (gegenbauer (1 : ℂ) n).eval z.val)
      (iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha 1) z) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_derivative_complexChebyshevSeries hρ ha z)
  simpa only [Finset.sum_range_one, Nat.cast_zero, T_zero, derivative_one, eval_zero,
    mul_zero, sub_zero, Nat.cast_add, Nat.cast_one, derivative_chebyshev_T_succ,
    eval_mul, eval_C, mul_assoc] using h

/-- Uniform convergence on compact subsets, with the limit evaluated only on its domain. -/
theorem tendstoUniformlyOn_derivative_complexChebyshevSeries {a : ℕ → ℂ} {C ρ r : ℝ}
    (hρ : 1 < ρ) (hr : 1 < r) (hrρ : r < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    {K : Set ℂ} (hK : IsCompact K) (hKr : K ⊆ bernsteinEllipse ⟨r, hr⟩) :
    TendstoUniformlyOn
      (fun N (z : bernsteinEllipse ⟨ρ, hρ⟩) ↦
        ∑ n ∈ Finset.range N, a n * (T ℂ n).derivative.eval z.val)
      (iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha 1))
      atTop {z | z.val ∈ K} := by
  have h := (tendstoUniformlyOn_derivative_series (isOpen_bernsteinEllipse ⟨r, hr⟩)
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ r / ρ)
      ((div_lt_one (by linarith : 0 < ρ)).2 hrρ)).mul_left C)
    (norm_chebyshev_term_le_geometric hρ hr ha) hK hKr).comp
    (fun z : bernsteinEllipse ⟨ρ, hρ⟩ ↦ z.val)
  have he (N : ℕ) (z : ℂ) :
      deriv (fun w ↦ ∑ n ∈ Finset.range N, a n * (T ℂ n).eval w) z =
        ∑ n ∈ Finset.range N, a n * (T ℂ n).derivative.eval z := by
    rw [deriv_fun_sum (fun (n : ℕ) _ ↦ ((T ℂ n).differentiable.const_mul (a n)).differentiableAt)]
    simp only [deriv_const_mul_field, Polynomial.deriv]
  simp only [Function.comp_def, he] at h
  exact h.congr_right (fun z _ ↦ by
    rw [iteratedDeriv_complexChebyshevSeries_eq, iteratedDeriv_one])

/-- First-order Cauchy truncation bound for the actual derivative value. -/
theorem norm_derivative_complexChebyshevSeries_sub_sum_le {a : ℕ → ℂ} {C ρ r δ : ℝ}
    (hρ : 1 < ρ) (hr : 1 < r) (hrρ : r < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    (z : bernsteinEllipse ⟨ρ, hρ⟩) (hz : z.val ∈ bernsteinEllipse ⟨r, hr⟩) (hδ : 0 < δ)
    (hball : Metric.sphere z.val δ ⊆ bernsteinEllipse ⟨r, hr⟩) (N : ℕ) :
    ‖iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha 1) z -
      ∑ n ∈ Finset.range N, a n * (T ℂ n).derivative.eval z.val‖ ≤
      C * (r / ρ) ^ N / (1 - r / ρ) / δ := by
  rw [iteratedDeriv_complexChebyshevSeries_eq, iteratedDeriv_one]
  have hq0 : 0 ≤ r / ρ := by positivity
  have hq1 : r / ρ < 1 := (div_lt_one (by linarith : 0 < ρ)).2 hrρ
  have h := norm_derivative_series_sub_sum_le (P := fun n ↦ T ℂ n) (a := a)
    (isOpen_bernsteinEllipse ⟨r, hr⟩) ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
    (norm_chebyshev_term_le_geometric hρ hr ha) hz hδ hball N
  simpa only [tsum_geometric_majorant_tail hq0 hq1 N] using h
/-- The corresponding uniform first-order bound. -/
theorem exists_uniform_derivative_series_bound {a : ℕ → ℂ} {C ρ r : ℝ}
    (hρ : 1 < ρ) (hr : 1 < r) (hrρ : r < ρ) (ha : ∀ n, ‖a n‖ ≤ C / ρ ^ n)
    {K : Set ℂ} (hK : IsCompact K) (hKr : K ⊆ bernsteinEllipse ⟨r, hr⟩) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : bernsteinEllipse ⟨ρ, hρ⟩, z.val ∈ K → ∀ N : ℕ,
      ‖iteratedDerivOnOpen (complexChebyshevSeriesDerivInput hρ ha 1) z -
        ∑ n ∈ Finset.range N, a n * (T ℂ n).derivative.eval z.val‖ ≤
        C * (r / ρ) ^ N / (1 - r / ρ) / δ := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (isOpen_bernsteinEllipse ⟨r, hr⟩) hKr
  refine ⟨δ, hδ, fun z hz N ↦ ?_⟩
  apply norm_derivative_complexChebyshevSeries_sub_sum_le hρ hr hrρ ha z (hKr hz) hδ
  exact Metric.sphere_subset_closedBall.trans ((Metric.closedBall_subset_cthickening hz δ).trans hsub)

end Polynomial.Chebyshev
