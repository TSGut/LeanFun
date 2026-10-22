/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.AnalyticCharacterization
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexCoefficientBounds
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.BestApproximation

/-! # Bernstein's converse theorem
Geometric polynomial approximation gives an analytic extension to the open
Bernstein ellipse, without an a priori continuity assumption on the interval.
Reference: ATAP, Theorem 8.3.
-/

public section
namespace Polynomial.Chebyshev
open Complex Set Filter
open scoped Topology

/-- A geometric uniform approximation by polynomials forces continuity of the
data. No degree restriction is needed for this step of ATAP 8.3. -/
theorem continuousOn_of_geometric_polynomial_approximation {f : ℝ → ℂ}
    {p : ℕ → ℂ[X]} {C ρ : ℝ} (hρ : 1 < ρ)
    (hb : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → ‖f x - (p n).eval (x : ℂ)‖ ≤ C / ρ ^ n) :
    ContinuousOn f (Icc (-1) 1) := by
  have hq0 : 0 ≤ ρ⁻¹ := by positivity
  have hq1 : ρ⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < ρ)).2 hρ
  have ht : Tendsto (fun n : ℕ ↦ C / ρ ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero, inv_pow, div_eq_mul_inv] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hu : TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) ↦ (p n).eval (x : ℂ)) f atTop
      (Icc (-1) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x hx
    simpa only [dist_eq_norm] using (hb n x hx).trans_lt hn
  exact hu.continuousOn (Eventually.of_forall (fun n ↦ by fun_prop)).frequently

/-- Polynomial approximation controls all positive-index coefficients; index
zero is absorbed into the constant (ATAP, proof of Theorem 8.3). -/
theorem coefficient_decay_of_geometric_polynomial_approximation {f : ℝ → ℂ}
    {p : ℕ → ℂ[X]} {C ρ : ℝ} (hρ : 1 < ρ)
    (hp : ∀ n, (p n).degree < ((n + 1 : ℕ) : WithBot ℕ))
    (hb : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → ‖f x - (p n).eval (x : ℂ)‖ ≤ C / ρ ^ n) :
    ∃ D : ℝ, ∀ n, ‖complexCoefficient (ComplexCoefficientInput.ofContinuousOn f
      (continuousOn_of_geometric_polynomial_approximation hρ hb) n)‖ ≤ D / ρ ^ n := by
  have hf := continuousOn_of_geometric_polynomial_approximation hρ hb
  have hC : 0 ≤ C := (norm_nonneg _).trans (by simpa using hb 0 0 (by norm_num))
  refine ⟨max ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn f hf 0))‖ (2 * C * ρ), ?_⟩
  intro n
  cases n with
  | zero => simp
  | succ k =>
    have hpk : ContinuousOn (fun x : ℝ ↦ (p k).eval (x : ℂ)) (Icc (-1) 1) := by fun_prop
    have hc := norm_complexCoefficient_le (f := fun x ↦ f x - (p k).eval (x : ℂ))
      (hf.sub hpk) (k + 1) (by positivity : 0 ≤ C / ρ ^ k) (hb k)
    rw [complexCoefficient_sub hf hpk, complexCoefficient_polynomial_eq_zero (hp k),
      sub_zero] at hc
    simp only [Nat.add_one_ne_zero, ite_eq_right, not_false_eq_true] at hc
    calc
      _ ≤ 2 * (C / ρ ^ k) := hc
      _ = (2 * C * ρ) / ρ ^ (k + 1) := by
        rw [pow_succ]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Bernstein's converse: degree-n errors bounded by C/rho^n imply analytic
continuation to the OPEN ellipse E_rho (ATAP, Theorem 8.3). -/
theorem exists_analytic_extension_of_geometric_polynomial_approximation {f : ℝ → ℂ}
    {p : ℕ → ℂ[X]} {C ρ : ℝ} (hρ : 1 < ρ)
    (hp : ∀ n, (p n).degree < ((n + 1 : ℕ) : WithBot ℕ))
    (hb : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → ‖f x - (p n).eval (x : ℂ)‖ ≤ C / ρ ^ n) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩) ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, F x = f x := by
  obtain ⟨D, hD⟩ := coefficient_decay_of_geometric_polynomial_approximation hρ hp hb
  exact exists_analytic_extension_of_coefficient_decay hρ
    (continuousOn_of_geometric_polynomial_approximation hρ hb) hD

/-- Geometric decay of the attained best uniform error gives analytic
continuation (ATAP 8.3, in best-approximation form). -/
theorem exists_analytic_extension_of_bestUniformError {f : C(Icc (-1 : ℝ) 1, ℂ)} {C ρ : ℝ}
    (hρ : 1 < ρ) (hb : ∀ n, bestUniformError n f ≤ C / ρ ^ n) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩) ∧
      ∀ x : Icc (-1 : ℝ) 1, F (x : ℂ) = f x := by
  classical
  choose p hp he using fun n ↦ exists_bestUniformError n f
  let g : ℝ → ℂ := fun x ↦ if hx : x ∈ Icc (-1 : ℝ) 1 then f ⟨x, hx⟩ else 0
  have hg : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → ‖g x - (p n).eval (x : ℂ)‖ ≤ C / ρ ^ n := by
    intro n x hx
    have h := (f - polynomialOnInterval (p n)).norm_coe_le_norm ⟨x, hx⟩
    rw [he n] at h
    have hh : ‖g x - (p n).eval (x : ℂ)‖ ≤ bestUniformError n f := by
      simpa only [g, dite_eq_left hx, ContinuousMap.sub_apply, polynomialOnInterval, ContinuousMap.coe_mk] using h
    exact hh.trans (hb n)
  obtain ⟨F, hF, hfg⟩ := exists_analytic_extension_of_geometric_polynomial_approximation hρ hp hg
  refine ⟨F, hF, fun x ↦ ?_⟩
  simpa only [g, dite_eq_left x.property] using hfg x x.property

end Polynomial.Chebyshev
