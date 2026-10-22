/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ComplexCompetitor

/-!
# Weighted and pointwise approximation of complex analytic functions

The same constants as in the real-valued theory follow directly from complex
orthogonal projection, without separate real-part and imaginary-part estimates.
References: DLMF 18.2(viii); ATAP, Theorem 8.2.
-/

public section
open Real Complex MeasureTheory Set
open scoped InnerProductSpace
namespace Polynomial.Sequence
variable {μ : Measure ℝ} {P : Sequence ℝ} (hμ : HasFiniteMoments μ)

/-- Complex orthogonal partial sums inherit the geometric weighted L² bound
from the complex Chebyshev competitor. -/
theorem IsOrthogonal.norm_sub_sum_integralCoefficientScalar_le_of_analytic
    (hP : P.IsOrthogonal μ) (hpos : HasPositiveDefiniteIntegral μ)
    (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℂ 2 μ) (hf : ∀ᵐ x ∂μ, f x = F x) (N : ℕ) :
    ‖f - ∑ i ∈ Finset.range (N + 1), P.integralCoefficientScalar ℂ μ (IntegralCoefficientInput.ofL2 hμ hpos (P i) (P.ne_zero i) f) •
      polynomialToL2Scalar ℂ hμ (P i)‖ ≤
      √(μ.real univ) * (2 * M / (ρ ^ N * (ρ - 1))) := by
  have hb := (hP.orthonormal_normalizedToL2Scalar ℂ hμ hpos).norm_sub_sum_inner_le_of_mem_span
    (Finset.range (N + 1)) f (complexChebyshevToL2 hμ ⟨(fun x : ℝ ↦ F x), Chebyshev.integrable_classicalMeasureT_complex (Chebyshev.continuousOn_real_of_analytic hρ hF)⟩ N)
    (complexChebyshevToL2_mem_span hμ hpos ⟨(fun x : ℝ ↦ F x), Chebyshev.integrable_classicalMeasureT_complex (Chebyshev.continuousOn_real_of_analytic hρ hF)⟩ N)
  simp only [inner_normalizedToL2Scalar_smul ℂ hμ hpos] at hb
  exact hb.trans (norm_sub_complexChebyshevToL2_le_of_analytic hμ hsupp hρ hF hM f hf N)

include hμ in
/-- The Christoffel-kernel pointwise error bound also holds for complex data,
with exactly the same constant as in the real-valued theorem. -/
theorem IsOrthogonal.norm_sub_partialSumValueScalar_le_kernel_of_analytic
    (hP : P.IsOrthogonal μ) (hpos : HasPositiveDefiniteIntegral μ)
    (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℂ 2 μ) (hf : ∀ᵐ x ∂μ, f x = F x) (N : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖F x - P.partialSumValueScalar ℂ μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N) x‖ ≤
      (1 + √(P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _)) * √(μ.real univ)) *
        (2 * M / (ρ ^ N * (ρ - 1))) := by
  let z := ∑ n ∈ Finset.range (N + 1), Chebyshev.complexCoefficient (Chebyshev.ComplexCoefficientInput.ofContinuousOn (fun t : ℝ ↦ F t) (Chebyshev.continuousOn_real_of_analytic hρ hF) n) *
    (((Chebyshev.T ℝ n).eval x : ℝ) : ℂ)
  have hc : ‖F x - z‖ ≤ 2 * M / (ρ ^ N * (ρ - 1)) :=
    Chebyshev.norm_sub_sum_complexCoefficient_le_of_analytic hρ hF hM hx N
  have hz : inner ℂ (P.kernelVectorScalar ℂ hμ ⟨N, fun i _ ↦ squaredNorm_pos hpos P i⟩ x) (complexChebyshevToL2 hμ ⟨(fun x : ℝ ↦ F x), Chebyshev.integrable_classicalMeasureT_complex (Chebyshev.continuousOn_real_of_analytic hρ hF)⟩ N) = z :=
    hP.inner_kernelVectorScalar_complexChebyshevToL2 hμ hpos ⟨(fun x : ℝ ↦ F x), Chebyshev.integrable_classicalMeasureT_complex (Chebyshev.continuousOn_real_of_analytic hρ hF)⟩ N x
  have hd : ‖P.partialSumValueScalar ℂ μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N) x - z‖ ≤
      √(P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _)) * (√(μ.real univ) * (2 * M / (ρ ^ N * (ρ - 1)))) := by
    rw [← inner_kernelVectorScalar ℂ hμ hpos, ← hz, ← inner_sub_right]
    apply (norm_inner_le_norm _ _).trans
    rw [hP.norm_kernelVectorScalar ℂ hμ hpos]
    exact mul_le_mul_of_nonneg_left
      (norm_sub_complexChebyshevToL2_le_of_analytic hμ hsupp hρ hF hM f hf N) (sqrt_nonneg _)
  calc
    _ ≤ ‖F x - z‖ + ‖z - P.partialSumValueScalar ℂ μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N) x‖ := by
      simpa only [dist_eq_norm] using dist_triangle (F x) z (P.partialSumValueScalar ℂ μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N) x)
    _ ≤ 2 * M / (ρ ^ N * (ρ - 1)) +
        √(P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _)) * (√(μ.real univ) * (2 * M / (ρ ^ N * (ρ - 1)))) := by
      rw [norm_sub_rev z]
      exact add_le_add hc hd
    _ = _ := by ring

end Polynomial.Sequence
