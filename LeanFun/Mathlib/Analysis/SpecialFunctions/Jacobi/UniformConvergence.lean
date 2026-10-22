/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Approximation
public import LeanFun.Mathlib.Analysis.SpecificLimits.PolynomialGeometric

/-!
# Uniform convergence of analytic Jacobi expansions

The explicit polynomial factor in the uniform error bound is dominated by
rho^N for every rho > 1. The full orthogonality range is retained.
References: DLMF 18.18; ATAP, Chapters 8 and 16.
-/

public section
open Real Complex MeasureTheory Set Filter
open scoped Topology

namespace Polynomial
variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
include hα hβ

/-- Analytic Jacobi partial sums converge uniformly on the closed interval,
including endpoints, for every alpha,beta > -1. -/
theorem tendstoUniformlyOn_sum_jacobiCoefficient_of_analytic {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℝ 2 (jacobiMeasure α β))
    (hf : ∀ᵐ x ∂jacobiMeasure α β, f x = (F x).re) :
    TendstoUniformlyOn (fun N x ↦ ∑ i ∈ Finset.range (N + 1),
      (jacobiCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f i)) * (jacobi α β i).eval x)
      (fun x : ℝ ↦ (F x).re) atTop (Icc (-1) 1) := by
  obtain ⟨k, hkα, hkβ, hks⟩ := exists_jacobiKernel_exponent α β
  apply tendstoUniformlyOn_of_polynomial_geometric_bound (3 * k + 3) hρ
    (A := √(jacobiKernelBound ⟨α, hα⟩ ⟨β, hβ⟩ k) * √((jacobiMeasure α β).real univ))
    (B := ρ - 1) (C := 2 * M)
  intro N x hx
  convert norm_sub_sum_jacobiCoefficient_le_uniform_of_analytic hα hβ hρ hF hM f hf
    k hkα hkβ hks N hx using 1
  ring

end Polynomial
