/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Connection

/-!
# Parity of Cartesian disk connection coefficients

Even factors restrict both support gaps to even integers.
Reference: Dunkl–Xu, symmetric Cartesian constructions.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial.CartesianDiskSystem
variable {μ ν : Measure ℝ}
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (h g : ℝ[X]) (l : ℕ)
    (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))
    (hμ : Polynomial.HasFiniteMoments μ) (hν : Polynomial.HasFiniteMoments ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (hg : ∀ᵐ x ∂ν, 0 ≤ g.eval x)

include hμ hν hx hh hg

/-- Inner parity forbids the interleaved inner-index diagonals. -/
theorem connectionEntry_eq_zero_of_inner_parity [ν.IsNegInvariant]
    (hgpar : ∀ x, g.eval (-x) = g.eval x) {n k m j : ℕ} (hkj : k % 2 ≠ j % 2) :
    S.connectionEntry T n k m j = 0 := by
  let := (hμ.diskOuterModification hx h hh l).isFiniteMeasure
  let := (hν.polynomialDensityMeasure g hg).isFiniteMeasure
  let := isNegInvariant_polynomialDensityMeasure_comap g ν hgpar
  dsimp only [connectionEntry, polynomial]
  rw [
    integralInner_cartesianDiskPolynomial (ae_mem_diskOuterModification hx h l)
      _ _ _ _ k j (by simp) (by simp) (S.inner_parity k) (T.inner_parity j),
    integralInner_eq_zero_of_opposite_parity
      (comp_neg_X_eq_of_coeff_parity k (S.inner_parity k))
      (comp_neg_X_eq_of_coeff_parity j (T.inner_parity j)) hkj, mul_zero]

/-- Outer parity removes the interleaved total-degree diagonals. -/
theorem connectionEntry_eq_zero_of_total_parity [μ.IsNegInvariant]
    (hpos : Polynomial.HasPositiveDefiniteIntegral μ) (hh0 : h ≠ 0)
    (hhpar : ∀ x, h.eval (-x) = h.eval x)
    {n k m j r : ℕ} (hk : k ≤ n) (hj : j ≤ m) (hkj : k=j+2*r)
    (hnm : n % 2 ≠ m % 2) : S.connectionEntry T n k m j = 0 := by
  rw [S.connectionEntry_of_degree_gap h g l T hμ hν hx hh hg n k m j r hkj]
  let := isNegInvariant_diskOuterMeasure μ k
  let := isNegInvariant_diskOuterModification μ h hhpar l
  let := isNegInvariant_diskOuterMeasure (diskOuterModification h l (μ.comap Subtype.val)) j
  have hPm := hμ.diskOuterMeasure hx k
  have hPp := hpos.diskOuterMeasure hμ hx k
  have hQm := (hμ.diskOuterModification hx h hh l).diskOuterMeasure
    (ae_mem_diskOuterModification hx h l) j
  have hQp := (hpos.diskOuterModification hμ hx h hh0 hh l).diskOuterMeasure
    (hμ.diskOuterModification hx h hh l) (ae_mem_diskOuterModification hx h l) j
  have hP := (S.outer_orthogonal_real k).comp_neg_X hPm hPp (n-k)
  have hQ := (T.outer_orthogonal_real j).comp_neg_X hQm hQp (m-j)
  have he : (((1-Polynomial.X^2)^r*S.outer k (n-k))).comp (-Polynomial.X) =
      Polynomial.C ((-1 : ℝ)^(n-k))*((1-Polynomial.X^2)^r*S.outer k (n-k)) := by
    simp only [mul_comp, pow_comp, sub_comp, one_comp, X_comp, neg_sq, hP]
    ring
  rw [integralInner_eq_zero_of_opposite_parity he hQ (by omega)
    (hi := hQm.integrable_mul _ _), zero_mul]

end MvPolynomial.CartesianDiskSystem
