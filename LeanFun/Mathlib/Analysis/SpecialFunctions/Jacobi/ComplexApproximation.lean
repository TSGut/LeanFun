/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UniformConvergence
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ComplexApproximation

/-!
# Complex Jacobi coefficients and analytic approximation

Complex-valued data use the same real Jacobi family, measure and normalization.
The weighted and uniform bounds retain the constants of the real-valued theory.
References: DLMF 18.18; ATAP, Chapters 8 and 16.
-/

public section
open Real Complex MeasureTheory Set Filter
namespace Polynomial

/-- Complex Jacobi coefficients on their classical input domain (DLMF 18.18). -/
@[expose] noncomputable def jacobiComplexCoefficient (α β : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℂ (jacobiMeasure α β) (jacobi α β n)) : ℂ :=
  ((∫ x, (jacobi α β n).eval x ^ 2 ∂jacobiMeasure α β : ℝ) : ℂ)⁻¹ *
    ∫ x, f.val x * (((jacobi α β n).eval x : ℝ) : ℂ) ∂jacobiMeasure α β

/-- The classical complex weighted formula (DLMF 18.18). -/
theorem jacobiComplexCoefficient_apply (α β : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℂ (jacobiMeasure α β) (jacobi α β n)) :
    jacobiComplexCoefficient α β f =
      ((∫ x, (jacobi α β n).eval x ^ 2 ∂jacobiMeasure α β : ℝ) : ℂ)⁻¹ *
        ∫ x, f.val x * (((jacobi α β n).eval x : ℝ) : ℂ) ∂jacobiMeasure α β := rfl

/-- Complex coefficients agree with real coefficients on admissible real data. -/
theorem jacobiComplexCoefficient_ofReal (α β : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℝ (jacobiMeasure α β) (jacobi α β n)) :
    jacobiComplexCoefficient α β f.ofReal = (jacobiCoefficient α β f : ℂ) := by
  simp only [jacobiComplexCoefficient, jacobiCoefficient, IntegralCoefficientInput.ofReal_val,
    ofReal_mul, ofReal_inv]
  congr 1
  simp_rw [← ofReal_mul]
  exact integral_complex_ofReal

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)

/-- The general scalar coefficient specializes on the full classical input domain. -/
theorem integralCoefficientScalar_jacobiSequence {n : ℕ}
    (f : IntegralCoefficientInput ℂ (jacobiMeasure α β) (jacobi α β n)) :
    (jacobiSequence hα hβ).integralCoefficientScalar ℂ (jacobiMeasure α β) f =
      jacobiComplexCoefficient α β f := by
  simp only [Sequence.integralCoefficientScalar, squaredNorm_jacobiSequence,
    jacobiSequence_apply, jacobiComplexCoefficient]
  rfl

/-- Internal specialization for L2 representatives. -/
theorem integralCoefficientScalar_jacobiSequence_L2 (f : Lp ℂ 2 (jacobiMeasure α β)) (n : ℕ) :
    (jacobiSequence hα hβ).integralCoefficientScalar ℂ (jacobiMeasure α β) (IntegralCoefficientInput.ofL2 (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) ((jacobiSequence hα hβ) n) ((jacobiSequence hα hβ).ne_zero n) f) =
      jacobiComplexCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f n) := by
  simp only [Sequence.integralCoefficientScalar, squaredNorm_jacobiSequence,
    jacobiSequence_apply, jacobiComplexCoefficient, IntegralCoefficientInput.ofJacobiL2,
    IntegralCoefficientInput.ofL2, RCLike.ofReal_eq_complex_ofReal]

/-- Geometric weighted L² error for complex analytic Jacobi expansions. -/
theorem norm_sub_sum_jacobiComplexCoefficient_le_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℂ 2 (jacobiMeasure α β)) (hf : ∀ᵐ x ∂jacobiMeasure α β, f x = F x) (N : ℕ) :
    ‖f - ∑ i ∈ Finset.range (N + 1), (jacobiComplexCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f i)) •
      polynomialToL2Scalar ℂ (hasFiniteMoments_jacobiMeasure hα hβ) (jacobi α β i)‖ ≤
      √((jacobiMeasure α β).real univ) * (2 * M / (ρ ^ N * (ρ - 1))) := by
  simpa only [Sequence.integralCoefficientScalar, squaredNorm_jacobiSequence, jacobiSequence_apply,
    jacobiComplexCoefficient, IntegralCoefficientInput.ofJacobiL2, IntegralCoefficientInput.ofL2, RCLike.ofReal_eq_complex_ofReal] using
    (isOrthogonal_jacobiSequence hα hβ).norm_sub_sum_integralCoefficientScalar_le_of_analytic
      (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)
      ((ae_mem_Ioo_jacobiMeasure α β).mono (fun _ hx ↦ Ioo_subset_Icc_self hx)) hρ hF hM f hf N

include hα hβ

/-- Uniform complex Jacobi approximation, with an explicit nonsharp polynomial factor. -/
theorem norm_sub_sum_jacobiComplexCoefficient_le_uniform_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℂ 2 (jacobiMeasure α β)) (hf : ∀ᵐ x ∂jacobiMeasure α β, f x = F x)
    (k : ℕ) (hkα : α + 1 ≤ k) (hkβ : β ≤ k) (hks : α + β + 1 ≤ k)
    (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖F x - ∑ i ∈ Finset.range (N + 1),
        (jacobiComplexCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f i)) * (((jacobi α β i).eval x : ℝ) : ℂ)‖ ≤
      (1 + √(jacobiKernelBound ⟨α, hα⟩ ⟨β, hβ⟩ k) * ((N : ℝ) + 1) ^ (3 * k + 3) *
        √((jacobiMeasure α β).real univ)) * (2 * M / (ρ ^ N * (ρ - 1))) := by
  have h := (isOrthogonal_jacobiSequence hα hβ).norm_sub_partialSumValueScalar_le_kernel_of_analytic
    (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)
    ((ae_mem_Ioo_jacobiMeasure α β).mono (fun _ hx ↦ Ioo_subset_Icc_self hx)) hρ hF hM f hf N hx
  simp only [Sequence.partialSumValueScalar_ofL2, Sequence.integralCoefficientScalar, squaredNorm_jacobiSequence,
    jacobiSequence_apply, jacobiComplexCoefficient, IntegralCoefficientInput.ofJacobiL2,
    IntegralCoefficientInput.ofL2, RCLike.ofReal_eq_complex_ofReal] at h ⊢
  have hM0 : 0 ≤ M := (norm_nonneg (F x)).trans (hM x (ofReal_mem_bernsteinEllipse hρ hx))
  apply h.trans
  gcongr
  exact sqrt_jacobi_kernel_le_polynomial hα hβ k hkα hkβ hks N hx

/-- Complex analytic Jacobi expansions converge uniformly on the closed interval. -/
theorem tendstoUniformlyOn_sum_jacobiComplexCoefficient_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℂ 2 (jacobiMeasure α β)) (hf : ∀ᵐ x ∂jacobiMeasure α β, f x = F x) :
    TendstoUniformlyOn (fun N x ↦ ∑ i ∈ Finset.range (N + 1),
      (jacobiComplexCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f i)) * (((jacobi α β i).eval x : ℝ) : ℂ))
      (fun x : ℝ ↦ F x) atTop (Icc (-1) 1) := by
  obtain ⟨k, hkα, hkβ, hks⟩ := exists_jacobiKernel_exponent α β
  apply tendstoUniformlyOn_of_polynomial_geometric_bound (3 * k + 3) hρ
    (A := √(jacobiKernelBound ⟨α, hα⟩ ⟨β, hβ⟩ k) * √((jacobiMeasure α β).real univ))
    (B := ρ - 1) (C := 2 * M)
  intro N x hx
  convert norm_sub_sum_jacobiComplexCoefficient_le_uniform_of_analytic hα hβ hρ hF hM f hf
    k hkα hkβ hks N hx using 1
  ring

end Polynomial
