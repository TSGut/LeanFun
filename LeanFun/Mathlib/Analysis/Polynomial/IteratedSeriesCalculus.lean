/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.SeriesCalculus
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Higher derivatives of normally convergent polynomial expansions
All orders share the same normal-convergence hypothesis. Cauchy's inequality
supplies factorial/radius error bounds. Reference: ATAP, Chapters 8 and 21.
-/

public section
namespace Polynomial
open Set Filter

/-- Analytic iterated derivatives agree with iterates of polynomial differentiation. -/
theorem iteratedDeriv_eval (p : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun z ↦ p.eval z) = fun z ↦ (derivative^[k] p).eval z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext z
    rw [iteratedDeriv_succ, ih, Polynomial.deriv]
    simp only [Function.iterate_succ_apply']

/-- Polynomial local uniform convergence passes to derivatives of every order. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv {ι : Type*} {Q : ι → ℂ[X]}
    {f : ℂ → ℂ} {φ : Filter ι} {U : Set ℂ} (hU : IsOpen U)
    (h : TendstoLocallyUniformlyOn (fun i z ↦ (Q i).eval z) f φ U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i z ↦ (derivative^[k] (Q i)).eval z)
      (iteratedDeriv k f) φ U := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hd := ih.deriv (Eventually.of_forall fun i ↦ (derivative^[k] (Q i)).differentiableOn) hU
    have he (p : ℂ[X]) : deriv (fun z ↦ p.eval z) = fun z ↦ p.derivative.eval z :=
      _root_.funext (fun _ ↦ p.deriv)
    simpa only [Function.comp_def, he, Function.iterate_succ_apply', iteratedDeriv_succ] using hd

/-- Every derivative of a normally convergent polynomial expansion is the
locally uniform limit of the corresponding differentiated finite sums. -/
theorem tendstoLocallyUniformlyOn_iterated_derivative_series {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun s : Finset ℕ ↦ fun z ↦ ∑ n ∈ s, a n * (derivative^[k] (P n)).eval z)
      (iteratedDeriv k (fun z ↦ ∑' n, a n * (P n).eval z)) atTop U := by
  let Q (s : Finset ℕ) : ℂ[X] := ∑ n ∈ s, a n • P n
  have hq : TendstoLocallyUniformlyOn (fun s z ↦ (Q s).eval z)
      (fun z ↦ ∑' n, a n * (P n).eval z) atTop U := by
    simpa only [Q, eval_finsetSum, eval_smul, smul_eq_mul] using
      (tendstoUniformlyOn_tsum hu hb).tendstoLocallyUniformlyOn
  have h := tendstoLocallyUniformlyOn_iteratedDeriv hU hq k
  have he (s : Finset ℕ) : derivative^[k] (Q s) = ∑ n ∈ s, a n • derivative^[k] (P n) := by
    simp only [Q, iterate_derivative_sum, iterate_derivative_smul]
  simpa only [he, eval_finsetSum, eval_smul, smul_eq_mul] using h

/-- On a compact subset, all differentiated finite sums converge uniformly. -/
theorem tendstoUniformlyOn_iterated_derivative_series {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U K : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    (hK : IsCompact K) (hKU : K ⊆ U) (k : ℕ) :
    TendstoUniformlyOn
      (fun s : Finset ℕ ↦ fun z ↦ ∑ n ∈ s, a n * (derivative^[k] (P n)).eval z)
      (iteratedDeriv k (fun z ↦ ∑' n, a n * (P n).eval z)) atTop K :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp
    (tendstoLocallyUniformlyOn_iterated_derivative_series hU hu hb k) K hKU hK

/-- Termwise differentiation to arbitrary order under the original majorant. -/
theorem hasSum_iterated_derivative_series {P : ℕ → ℂ[X]} {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n) (k : ℕ)
    {z : ℂ} (hz : z ∈ U) :
    HasSum (fun n ↦ a n * (derivative^[k] (P n)).eval z)
      (iteratedDeriv k (fun w ↦ ∑' n, a n * (P n).eval w) z) := by
  change Tendsto (fun s : Finset ℕ ↦ ∑ n ∈ s, a n * (derivative^[k] (P n)).eval z)
    atTop (nhds (iteratedDeriv k (fun w ↦ ∑' n, a n * (P n).eval w) z))
  exact (tendstoLocallyUniformlyOn_iterated_derivative_series (P := P) (a := a)
    hU hu hb k).tendsto_at hz

/-- An order-k truncation error is bounded by k!/delta^k times the original
majorant tail, including k=0. -/
theorem norm_iterated_derivative_series_sub_sum_le {P : ℕ → ℂ[X]} {a : ℕ → ℂ}
    {u : ℕ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (P n).eval z‖ ≤ u n)
    (k : ℕ) {z : ℂ} (hz : z ∈ U) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.sphere z δ ⊆ U) (N : ℕ) :
    ‖iteratedDeriv k (fun w ↦ ∑' n, a n * (P n).eval w) z -
      ∑ n ∈ Finset.range N, a n * (derivative^[k] (P n)).eval z‖ ≤
      k.factorial * (∑' n, u (n + N)) / δ ^ k := by
  have hd (n : ℕ) : ‖a n * (derivative^[k] (P n)).eval z‖ ≤ k.factorial * u n / δ ^ k := by
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (f := fun w : ℂ ↦ a n * (P n).eval w) (C := u n) (c := z) (R := δ) k hδ
      ((P n).differentiable.const_mul (a n)).diffContOnCl
      (fun w hw ↦ hb n w (hball hw))
    simpa only [iteratedDeriv_const_mul_field, iteratedDeriv_eval] using h
  have h := norm_series_sub_sum_le_tail (hasSum_iterated_derivative_series (P := P) (a := a) hU hu hb k hz)
    ((hu.mul_left (k.factorial : ℝ)).div_const (δ ^ k)) hd N
  simpa only [tsum_div_const, tsum_mul_left] using h

end Polynomial
