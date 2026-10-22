/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Quadrature
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.QuadratureError
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RealApproximation

/-! # Geometric Gauss--Jacobi quadrature error
An analytic Chebyshev competitor of degree `2*n-1` and positive Gaussian
weights give geometric convergence for every Jacobi weight with parameters
above -1. Reference: ATAP, proof of Theorem 19.3; DLMF §3.5(v).
-/

public section
namespace Polynomial
open MeasureTheory Set Complex

/-- Gauss--Jacobi error from a real polynomial competitor (ATAP, proof of 19.3). -/
theorem abs_integral_sub_jacobiGauss_le_of_competitor
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : 1 ≤ n)
    {f : ℝ → ℝ} (hf : Integrable f (jacobiMeasure α β))
    {p : ℝ[X]} (hp : p.degree < (2 * n : ℕ)) {ε : ℝ}
    (he : ∀ x ∈ Icc (-1 : ℝ) 1, |f x - p.eval x| ≤ ε) :
    |(∫ x, f x ∂jacobiMeasure α β) -
      ∑ x ∈ (jacobi α β n).roots.toFinset, jacobiGaussWeight α β n x (Lagrange.QuadratureInput.ofMoments (hasFiniteMoments_jacobiMeasure hα hβ) (Lagrange.BasisInput.id _ _)) * f x| ≤
      2 * (jacobiMeasure α β).real univ * ε := by
  apply (isOrthogonal_jacobiSequence hα hβ).abs_integral_sub_gauss_le_of_competitor
    (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) hn hf hp
  · filter_upwards [ae_mem_Ioo_jacobiMeasure α β] with x hx
    exact he x (Ioo_subset_Icc_self hx)
  · intro x hx
    exact he x (Ioo_subset_Icc_self (jacobiGaussNodes_subset_Ioo hα hβ n hx))

/-- Baseline geometric error for the `n`-point Gauss--Jacobi rule. Analyticity
and boundedness are needed only on the open ellipse; the measure retains its
original mass normalisation (ATAP, proof of Theorem 19.3). -/
theorem abs_integral_sub_jacobiGauss_le_of_analytic
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : 1 ≤ n)
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M) :
    |(∫ x, (F x).re ∂jacobiMeasure α β) -
      ∑ x ∈ (jacobi α β n).roots.toFinset,
        jacobiGaussWeight α β n x (Lagrange.QuadratureInput.ofMoments (hasFiniteMoments_jacobiMeasure hα hβ) (Lagrange.BasisInput.id _ _)) * (F x).re| ≤
      4 * (jacobiMeasure α β).real univ * M / (ρ ^ (2 * n - 1) * (ρ - 1)) := by
  obtain ⟨p, hp, he⟩ := Chebyshev.exists_real_polynomial_approximation_of_analytic
    hρ hF hM (2 * n - 1)
  have hd : p.degree < (2 * n : ℕ) := hp.trans_lt (by
    exact_mod_cast (show 2 * n - 1 < 2 * n by omega))
  have hc : ContinuousOn (fun x : ℝ ↦ (F x).re) (Icc (-1) 1) :=
    Complex.continuous_re.continuousOn.comp
      (hF.continuousOn.comp Complex.continuous_ofReal.continuousOn
        (fun x hx ↦ ofReal_mem_bernsteinEllipse hρ hx)) (fun _ _ ↦ mem_univ _)
  have h := abs_integral_sub_jacobiGauss_le_of_competitor hα hβ hn
    (integrable_jacobiMeasure hα hβ hc) hd
    (fun x hx ↦ by simpa only [Real.norm_eq_abs] using he x hx)
  convert h using 1
  ring

end Polynomial
