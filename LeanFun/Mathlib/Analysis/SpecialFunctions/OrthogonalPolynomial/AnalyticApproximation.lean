/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.KernelBound
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RealApproximation

/-!
# Geometric weighted L² error bounds

An analytic Chebyshev competitor transfers its error bound to every orthogonal
polynomial projection for a measure supported on [-1,1], including disconnected
supports. References: ATAP, Theorems 8.2 and the best-approximation principle.
-/

public section
open Real Complex MeasureTheory Set
namespace Polynomial.Sequence
variable {μ : Measure ℝ} {P : Sequence ℝ} (hμ : HasFiniteMoments μ)

/-- The real part of a bounded analytic function has geometrically accurate
weighted orthogonal projections. The measure need not have connected support. -/
theorem IsOrthogonal.norm_sub_sum_integralCoefficient_le_of_analytic
    (hP : P.IsOrthogonal μ) (hpos : HasPositiveDefiniteIntegral μ)
    (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x = (F x).re) (N : ℕ) :
    ‖f - ∑ i ∈ Finset.range (N + 1),
      P.integralCoefficient μ (IntegralCoefficientInput.ofL2 hμ hpos (P i) (P.ne_zero i) f) • polynomialToL2 hμ (P i)‖ ≤
      √(μ.real univ) * (2 * M / (ρ ^ N * (ρ - 1))) := by
  obtain ⟨p, hp, he⟩ := Chebyshev.exists_real_polynomial_approximation_of_analytic hρ hF hM N
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans
    (hM 0 (by simpa using (ofReal_mem_bernsteinEllipse hρ
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num))))
  apply hP.norm_sub_sum_integralCoefficient_le_of_ae_bound hμ hpos f N p hp
    (by positivity)
  filter_upwards [hf, hsupp] with x hfx hx
  rw [hfx]
  exact he x hx

include hμ in
/-- The analytic competitor also gives a pointwise bound for the actual
orthogonal partial sum, with its Christoffel kernel factor displayed. -/
theorem IsOrthogonal.norm_sub_eval_partialSum_le_kernel_of_analytic
    (hP : P.IsOrthogonal μ) (hpos : HasPositiveDefiniteIntegral μ)
    (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x = (F x).re)
    (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖(F x).re - (P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N)).eval x‖ ≤
      (1 + √(P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _)) * √(μ.real univ)) *
        (2 * M / (ρ ^ N * (ρ - 1))) := by
  obtain ⟨p, hp, he⟩ := Chebyshev.exists_real_polynomial_approximation_of_analytic hρ hF hM N
  have hM0 : 0 ≤ M := (norm_nonneg (F x)).trans
    (hM x (ofReal_mem_bernsteinEllipse hρ hx))
  apply hP.norm_sub_eval_partialSum_le_kernel hμ hpos f N p hp (by positivity) _ x (F x).re
    (he x hx)
  filter_upwards [hf, hsupp] with t hft ht
  rw [hft]
  exact he t ht

end Polynomial.Sequence
