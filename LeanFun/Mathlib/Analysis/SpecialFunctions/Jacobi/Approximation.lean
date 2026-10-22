/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.KernelBounds
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.AnalyticApproximation

/-!
# Quantitative weighted L² approximation by Jacobi expansions

The entire orthogonality range alpha,beta > -1 is retained, including singular
endpoint weights. References: DLMF 18.18; ATAP, Chapters 8 and 16.
-/

public section
open Real Complex MeasureTheory Set
namespace Polynomial
variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)

/-- Jacobi truncation is a best weighted L² approximation among polynomials of
at most the same degree. -/
theorem norm_sub_sum_jacobiCoefficient_le (f : Lp ℝ 2 (jacobiMeasure α β))
    (N : ℕ) (p : ℝ[X]) (hp : p.degree ≤ N) :
    ‖f - ∑ i ∈ Finset.range (N + 1), (jacobiCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f i)) •
      polynomialToL2 (hasFiniteMoments_jacobiMeasure hα hβ) (jacobi α β i)‖ ≤
      ‖f - polynomialToL2 (hasFiniteMoments_jacobiMeasure hα hβ) p‖ := by
  simpa only [Sequence.integralCoefficient, squaredNorm_jacobiSequence, jacobiSequence_apply,
    jacobiCoefficient, IntegralCoefficientInput.ofJacobiL2, IntegralCoefficientInput.ofL2] using
    (isOrthogonal_jacobiSequence hα hβ).norm_sub_sum_integralCoefficient_le
      (hasFiniteMoments_jacobiMeasure hα hβ)
      (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) f N p hp

/-- Geometric Jacobi truncation error for the real part of a bounded analytic
function on an open Bernstein ellipse, for every alpha,beta > -1. -/
theorem norm_sub_sum_jacobiCoefficient_le_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℝ 2 (jacobiMeasure α β))
    (hf : ∀ᵐ x ∂jacobiMeasure α β, f x = (F x).re) (N : ℕ) :
    ‖f - ∑ i ∈ Finset.range (N + 1), (jacobiCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f i)) •
      polynomialToL2 (hasFiniteMoments_jacobiMeasure hα hβ) (jacobi α β i)‖ ≤
      √((jacobiMeasure α β).real univ) * (2 * M / (ρ ^ N * (ρ - 1))) := by
  simpa only [Sequence.integralCoefficient, squaredNorm_jacobiSequence, jacobiSequence_apply,
    jacobiCoefficient, IntegralCoefficientInput.ofJacobiL2, IntegralCoefficientInput.ofL2] using
    (isOrthogonal_jacobiSequence hα hβ).norm_sub_sum_integralCoefficient_le_of_analytic
      (hasFiniteMoments_jacobiMeasure hα hβ)
      (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)
      ((ae_mem_Ioo_jacobiMeasure α β).mono (fun _ hx ↦ Ioo_subset_Icc_self hx))
      hρ hF hM f hf N

include hα hβ in
/-- Uniform geometric approximation with an explicit nonsharp polynomial factor.
Every alpha,beta > -1 is covered by choosing a sufficiently large integer k. -/
theorem norm_sub_sum_jacobiCoefficient_le_uniform_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℝ 2 (jacobiMeasure α β))
    (hf : ∀ᵐ x ∂jacobiMeasure α β, f x = (F x).re)
    (k : ℕ) (hkα : α + 1 ≤ k) (hkβ : β ≤ k) (hks : α + β + 1 ≤ k)
    (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖(F x).re - ∑ i ∈ Finset.range (N + 1),
        (jacobiCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f i)) * (jacobi α β i).eval x‖ ≤
      (1 + √(jacobiKernelBound ⟨α, hα⟩ ⟨β, hβ⟩ k) * ((N : ℝ) + 1) ^ (3 * k + 3) *
        √((jacobiMeasure α β).real univ)) * (2 * M / (ρ ^ N * (ρ - 1))) := by
  have h := (isOrthogonal_jacobiSequence hα hβ).norm_sub_eval_partialSum_le_kernel_of_analytic
    (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)
    ((ae_mem_Ioo_jacobiMeasure α β).mono (fun _ hx ↦ Ioo_subset_Icc_self hx)) hρ hF hM f hf N hx
  simp only [Sequence.partialSum_ofL2, eval_finsetSum, eval_smul, smul_eq_mul,
    Sequence.integralCoefficient, squaredNorm_jacobiSequence, jacobiSequence_apply,
    IntegralCoefficientInput.ofL2] at h
  have hM0 : 0 ≤ M := (norm_nonneg (F x)).trans (hM x (ofReal_mem_bernsteinEllipse hρ hx))
  apply h.trans
  gcongr
  exact sqrt_jacobi_kernel_le_polynomial hα hβ k hkα hkβ hks N hx

end Polynomial
