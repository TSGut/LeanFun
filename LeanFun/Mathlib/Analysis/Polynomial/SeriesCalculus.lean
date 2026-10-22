/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Calculus of polynomial expansions
Family-independent normal-convergence and integration results used by spectral
coefficient calculus. Reference: ATAP, Chapters 8 and 21.
-/

public section
open Set Filter MeasureTheory
open scoped Topology
namespace Polynomial

/-- A summable uniform majorant permits differentiation of a complex polynomial
expansion on an open set. No orthogonality or interval hypothesis is needed. -/
theorem hasSum_derivative_series {P : ℕ → ℂ[X]} {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n) {z : ℂ} (hz : z ∈ U) :
    HasSum (fun n ↦ a n * (P n).derivative.eval z)
      (deriv (fun w ↦ ∑' n, a n * (P n).eval w) z) := by
  have h := Complex.hasSum_deriv_of_summable_norm hu
    (fun n ↦ ((P n).differentiable.const_mul (a n)).differentiableOn) hU hb hz
  simpa only [deriv_const_mul_field, Polynomial.deriv] using h

/-- Derivatives of polynomial partial sums converge uniformly on compact
subsets of the open domain of normal convergence. -/
theorem tendstoUniformlyOn_derivative_series {P : ℕ → ℂ[X]} {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U K : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun N ↦ deriv (fun z ↦ ∑ n ∈ Finset.range N, a n * (P n).eval z))
      (deriv (fun z ↦ ∑' n, a n * (P n).eval z)) atTop K := by
  have h := (tendstoUniformlyOn_tsum_nat hu hb).tendstoLocallyUniformlyOn.deriv
    (Eventually.of_forall fun N ↦ DifferentiableOn.fun_sum fun n _ ↦
      ((P n).differentiable.const_mul (a n)).differentiableOn) hU
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp h K hKU hK

/-- A summable uniform majorant permits termwise integration on any compact
real interval, for complex-valued expansions. -/
theorem hasSum_integral_series {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ} {u : ℕ → ℝ} {a b : ℝ}
    (hF : ∀ n, Continuous (F n)) (hu : Summable u)
    (hb : ∀ n x, x ∈ uIcc a b → ‖F n x‖ ≤ u n)
    (hf : ∀ x ∈ uIcc a b, HasSum (fun n ↦ F n x) (f x)) :
    HasSum (fun n ↦ ∫ x in a..b, F n x) (∫ x in a..b, f x) := by
  exact intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ ↦ u n)
    (fun n ↦ (hF n).aestronglyMeasurable)
    (fun n ↦ Eventually.of_forall fun x hx ↦ hb n x (uIoc_subset_uIcc hx))
    (Eventually.of_forall fun _ _ ↦ hu) intervalIntegrable_const
    (Eventually.of_forall fun x hx ↦ hf x (uIoc_subset_uIcc hx))

/-- Any norm-majorized series has a truncation bound by the corresponding tail.
This is shared by derivative, primitive and product expansions. -/
theorem norm_series_sub_sum_le_tail {f : ℕ → ℂ} {v : ℕ → ℝ} {s : ℂ}
    (hs : HasSum f s) (hv : Summable v) (hb : ∀ n, ‖f n‖ ≤ v n) (N : ℕ) :
    ‖s - ∑ n ∈ Finset.range N, f n‖ ≤ ∑' n, v (n + N) := by
  have he := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at he
  have ht : s - ∑ n ∈ Finset.range N, f n = ∑' n, f (n + N) := by
    rw [← he]; abel
  rw [ht]
  have hn : Summable (fun n ↦ ‖f (n + N)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ hb (n + N))
      ((summable_nat_add_iff N).2 hv)
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun n ↦ hb (n + N)) ((summable_nat_add_iff N).2 hv))

/-- A circle inside the domain gives a derivative truncation estimate by
Cauchy's inequality. The same radius may be used uniformly over a compact set. -/
theorem norm_derivative_series_sub_sum_le {P : ℕ → ℂ[X]} {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    {z : ℂ} (hz : z ∈ U) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.sphere z δ ⊆ U) (N : ℕ) :
    ‖deriv (fun w ↦ ∑' n, a n * (P n).eval w) z -
      ∑ n ∈ Finset.range N, a n * (P n).derivative.eval z‖ ≤
      (∑' n, u (n + N)) / δ := by
  have hd (n : ℕ) : ‖a n * (P n).derivative.eval z‖ ≤ u n / δ := by
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      ((P n).differentiable.const_mul (a n)).diffContOnCl
      (fun w hw ↦ hb n w (hball hw))
    simpa only [deriv_const_mul_field, Polynomial.deriv] using h
  have h := norm_series_sub_sum_le_tail (hasSum_derivative_series hU hu hb hz)
    (hu.div_const δ) hd N
  simpa only [tsum_div_const] using h

end Polynomial
