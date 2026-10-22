/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Projection

/-!
# From weighted L² to uniform approximation

A bound on degree-N polynomial evaluation transfers a uniform competitor error
to a pointwise error for the weighted orthogonal projection. The evaluation
constant is an explicit hypothesis; no growth rate is asserted here.
Reference: the Christoffel-function method; DLMF 18.2(viii); ATAP, Chapter 16.
-/

public section
open Real MeasureTheory
namespace Polynomial.Sequence
variable {μ : Measure ℝ} {P : Sequence ℝ} (hμ : HasFiniteMoments μ)

/-- Any polynomial inverse bound transfers a uniform competitor estimate to
pointwise error of weighted orthogonal projection. -/
theorem IsOrthogonal.norm_sub_eval_partialSum_le_of_polynomial_bound
    (hP : P.IsOrthogonal μ) (hpos : HasPositiveDefiniteIntegral μ)
    (f : Lp ℝ 2 μ) (N : ℕ) (p : ℝ[X]) (hp : p.degree ≤ N)
    {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (he : ∀ᵐ t ∂μ, ‖f t - p.eval t‖ ≤ ε) (x y : ℝ)
    (hx : ‖y - p.eval x‖ ≤ ε)
    (hbound : ∀ q : ℝ[X], q.degree ≤ N →
      ‖q.eval x‖ ≤ K * ‖polynomialToL2 hμ q‖) :
    ‖y - (P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N)).eval x‖ ≤
      (1 + K * √(μ.real Set.univ)) * ε := by
  have hd : P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P (f - polynomialToL2 hμ p : Lp ℝ 2 μ) N) =
      P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N) - p := by
    rw [partialSum_sub hμ hpos, hP.partialSum_polynomialToL2 hμ hpos N p hp]
  have hb := hbound _ (P.degree_partialSum_le (IntegralCoefficientFamilyInput.ofL2 hμ hpos P (f - polynomialToL2 hμ p : Lp ℝ 2 μ) N))
  have hc := hP.norm_polynomialToL2_partialSum_le hμ hpos
    (f - polynomialToL2 hμ p) N
  have hl := norm_sub_polynomialToL2_le_of_ae_bound hμ f p hε he
  have hval : ‖(P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N)).eval x - p.eval x‖ ≤
      K * (√(μ.real Set.univ) * ε) := by
    rw [hd, eval_sub] at hb
    rw [hd] at hc
    exact hb.trans (mul_le_mul_of_nonneg_left (hc.trans hl) hK)
  calc
    _ ≤ ‖y - p.eval x‖ + ‖p.eval x - (P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N)).eval x‖ := by
      simpa only [dist_eq_norm] using dist_triangle y (p.eval x) ((P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N)).eval x)
    _ ≤ ε + K * (√(μ.real Set.univ) * ε) := by
      rw [norm_sub_rev (p.eval x)]
      exact add_le_add hx hval
    _ = _ := by ring

end Polynomial.Sequence
