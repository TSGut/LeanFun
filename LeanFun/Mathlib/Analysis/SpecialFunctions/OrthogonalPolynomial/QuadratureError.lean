/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Quadrature
public import LeanFun.Mathlib.MeasureTheory.Integral.Quadrature

/-! # Gaussian quadrature error from polynomial approximation
Positive Gaussian weights transfer approximation error without assuming
connected or interval support. Reference: ATAP, proof of Theorem 19.3.
-/

public section
namespace Polynomial.Sequence
open MeasureTheory Set

/-- A polynomial competitor of degree below `2*n` controls the `n`-node Gaussian
error on any admissible measure. Bounds at nodes are separate from the a.e. bound
(ATAP, proof of Theorem 19.3). -/
theorem IsOrthogonal.abs_integral_sub_gauss_le_of_competitor
    {P : Sequence ℝ} {μ : Measure ℝ} (hP : P.IsOrthogonal μ)
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {n : ℕ} (hn : 1 ≤ n) {f : ℝ → ℝ} (hf : Integrable f μ)
    {p : ℝ[X]} (hp : p.degree < (2 * n : ℕ)) {ε : ℝ}
    (hae : ∀ᵐ x ∂μ, |f x - p.eval x| ≤ ε)
    (hnodes : ∀ x ∈ (P n).roots.toFinset, |f x - p.eval x| ≤ ε) :
    |(∫ x, f x ∂μ) - ∑ x ∈ (P n).roots.toFinset, P.gaussWeight μ n x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) * f x| ≤
      2 * μ.real univ * ε := by
  have := hμ.isFiniteMeasure
  apply abs_integral_sub_sum_le_of_nonneg_weights (P n).roots.toFinset id
    (fun x ↦ P.gaussWeight μ n x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _))) (fun x hx ↦ (hP.gaussWeight_pos hμ hpos hx).le)
    (hP.sum_gaussWeight hμ hpos hn) hf (g := fun x ↦ p.eval x)
  · simpa using hμ.integrable_mul p 1
  · exact hP.integral_eq_sum_gaussWeight_mul_eval hμ hpos hp
  · exact hae
  · exact hnodes

end Polynomial.Sequence
