/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Approximation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ComplexApproximation

/-!
# Complex Gegenbauer coefficients and analytic approximation

The scalar extension preserves the independent Gegenbauer family and the exact
symmetric-Jacobi kernel bridge. References: DLMF 18.7.1, 18.18; ATAP, Chapter 8.
-/

public section
open Real Complex MeasureTheory Set Filter
namespace Polynomial

/-- Complex Gegenbauer coefficients on their classical input domain (DLMF 18.18). -/
@[expose] noncomputable def gegenbauerComplexCoefficient (lam : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℂ (gegenbauerMeasure lam) (gegenbauer lam n)) : ℂ :=
  ((∫ x, (gegenbauer lam n).eval x ^ 2 ∂gegenbauerMeasure lam : ℝ) : ℂ)⁻¹ *
    ∫ x, f.val x * (((gegenbauer lam n).eval x : ℝ) : ℂ) ∂gegenbauerMeasure lam

/-- The classical complex weighted formula (DLMF 18.18). -/
theorem gegenbauerComplexCoefficient_apply (lam : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℂ (gegenbauerMeasure lam) (gegenbauer lam n)) :
    gegenbauerComplexCoefficient lam f =
      ((∫ x, (gegenbauer lam n).eval x ^ 2 ∂gegenbauerMeasure lam : ℝ) : ℂ)⁻¹ *
        ∫ x, f.val x * (((gegenbauer lam n).eval x : ℝ) : ℂ) ∂gegenbauerMeasure lam := rfl

/-- Complex coefficients agree with real coefficients on admissible real data. -/
theorem gegenbauerComplexCoefficient_ofReal (lam : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℝ (gegenbauerMeasure lam) (gegenbauer lam n)) :
    gegenbauerComplexCoefficient lam f.ofReal = (gegenbauerCoefficient lam f : ℂ) := by
  simp only [gegenbauerComplexCoefficient, gegenbauerCoefficient, IntegralCoefficientInput.ofReal_val,
    ofReal_mul, ofReal_inv]
  congr 1
  simp_rw [← ofReal_mul]
  exact integral_complex_ofReal

variable {lam : ℝ} (hlam : -(1 / 2) < lam) (hzero : lam ≠ 0)

/-- The general scalar coefficient specializes on the full classical input domain. -/
theorem integralCoefficientScalar_gegenbauerSequence {n : ℕ}
    (f : IntegralCoefficientInput ℂ (gegenbauerMeasure lam) (gegenbauer lam n)) :
    (gegenbauerSequence hlam hzero).integralCoefficientScalar ℂ (gegenbauerMeasure lam) f =
      gegenbauerComplexCoefficient lam f := by
  simp only [Sequence.integralCoefficientScalar, squaredNorm_gegenbauerSequence,
    gegenbauerSequence_apply, gegenbauerComplexCoefficient]
  rfl

/-- Internal specialization for L2 representatives. -/
theorem integralCoefficientScalar_gegenbauerSequence_L2 (f : Lp ℂ 2 (gegenbauerMeasure lam)) (n : ℕ) :
    (gegenbauerSequence hlam hzero).integralCoefficientScalar ℂ (gegenbauerMeasure lam) (IntegralCoefficientInput.ofL2 (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) ((gegenbauerSequence hlam hzero) n) ((gegenbauerSequence hlam hzero).ne_zero n) f) =
      gegenbauerComplexCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f n) := by
  simp only [Sequence.integralCoefficientScalar, squaredNorm_gegenbauerSequence,
    gegenbauerSequence_apply, gegenbauerComplexCoefficient, IntegralCoefficientInput.ofGegenbauerL2,
    IntegralCoefficientInput.ofL2, RCLike.ofReal_eq_complex_ofReal]

/-- Geometric weighted L² error for complex analytic Gegenbauer expansions. -/
theorem norm_sub_sum_gegenbauerComplexCoefficient_le_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℂ 2 (gegenbauerMeasure lam)) (hf : ∀ᵐ x ∂gegenbauerMeasure lam, f x = F x) (N : ℕ) :
    ‖f - ∑ i ∈ Finset.range (N + 1), (gegenbauerComplexCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f i)) •
      polynomialToL2Scalar ℂ (hasFiniteMoments_gegenbauerMeasure hlam) (gegenbauer lam i)‖ ≤
      √((gegenbauerMeasure lam).real univ) * (2 * M / (ρ ^ N * (ρ - 1))) := by
  have hP := isOrthogonal_gegenbauerSequence hlam hzero
  simpa only [Sequence.integralCoefficientScalar, squaredNorm_gegenbauerSequence, gegenbauerSequence_apply,
    gegenbauerComplexCoefficient, IntegralCoefficientInput.ofGegenbauerL2, IntegralCoefficientInput.ofL2, RCLike.ofReal_eq_complex_ofReal] using
    hP.norm_sub_sum_integralCoefficientScalar_le_of_analytic
      (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)
      ((ae_mem_Ioo_gegenbauerMeasure lam).mono (fun _ hx ↦ Ioo_subset_Icc_self hx)) hρ hF hM f hf N

/-- Uniform complex Gegenbauer approximation throughout the nondegenerate range. -/
theorem norm_sub_sum_gegenbauerComplexCoefficient_le_uniform_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℂ 2 (gegenbauerMeasure lam)) (hf : ∀ᵐ x ∂gegenbauerMeasure lam, f x = F x)
    (k : ℕ) (hk : lam + 1 / 2 ≤ k) (hks : 2 * lam ≤ k)
    (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖F x - ∑ i ∈ Finset.range (N + 1),
        (gegenbauerComplexCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f i)) * (((gegenbauer lam i).eval x : ℝ) : ℂ)‖ ≤
      (1 + √(jacobiKernelBound ⟨lam - 1 / 2, by change -1 < lam - 1 / 2; linarith⟩ ⟨lam - 1 / 2, by change -1 < lam - 1 / 2; linarith⟩ k) *
        ((N : ℝ) + 1) ^ (3 * k + 3) * √((gegenbauerMeasure lam).real univ)) *
        (2 * M / (ρ ^ N * (ρ - 1))) := by
  have hP := isOrthogonal_gegenbauerSequence hlam hzero
  have h := hP.norm_sub_partialSumValueScalar_le_kernel_of_analytic
      (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)
      ((ae_mem_Ioo_gegenbauerMeasure lam).mono (fun _ hx ↦ Ioo_subset_Icc_self hx))
      hρ hF hM f hf N hx
  simp only [Sequence.partialSumValueScalar_ofL2, Sequence.integralCoefficientScalar, squaredNorm_gegenbauerSequence,
    gegenbauerSequence_apply, gegenbauerComplexCoefficient, IntegralCoefficientInput.ofGegenbauerL2,
    IntegralCoefficientInput.ofL2, RCLike.ofReal_eq_complex_ofReal, gegenbauer_kernel_eq_jacobi hlam hzero] at h ⊢
  have hM0 : 0 ≤ M := (norm_nonneg (F x)).trans (hM x (ofReal_mem_bernsteinEllipse hρ hx))
  apply h.trans
  gcongr
  exact sqrt_jacobi_kernel_le_polynomial (by linarith) (by linarith) k
    (by linarith) (by linarith) (by linarith) N hx

/-- Complex analytic Gegenbauer expansions converge uniformly on the closed interval. -/
theorem tendstoUniformlyOn_sum_gegenbauerComplexCoefficient_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℂ 2 (gegenbauerMeasure lam)) (hf : ∀ᵐ x ∂gegenbauerMeasure lam, f x = F x) :
    TendstoUniformlyOn (fun N x ↦ ∑ i ∈ Finset.range (N + 1),
      (gegenbauerComplexCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f i)) * (((gegenbauer lam i).eval x : ℝ) : ℂ))
      (fun x : ℝ ↦ F x) atTop (Icc (-1) 1) := by
  obtain ⟨k, hk0, hks⟩ := exists_gegenbauerKernel_exponent lam
  apply tendstoUniformlyOn_of_polynomial_geometric_bound (3 * k + 3) hρ
    (A := √(jacobiKernelBound ⟨lam - 1 / 2, by change -1 < lam - 1 / 2; linarith⟩ ⟨lam - 1 / 2, by change -1 < lam - 1 / 2; linarith⟩ k) *
      √((gegenbauerMeasure lam).real univ)) (B := ρ - 1) (C := 2 * M)
  intro N x hx
  convert norm_sub_sum_gegenbauerComplexCoefficient_le_uniform_of_analytic hlam hzero hρ hF hM f hf
    k hk0 hks N hx using 1
  ring

end Polynomial
