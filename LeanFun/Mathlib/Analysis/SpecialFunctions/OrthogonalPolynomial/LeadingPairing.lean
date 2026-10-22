/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Uniqueness

/-! # Leading-degree orthogonal pairings
The top coordinate of a polynomial depends only on its leading coefficient.
This determines strict signs of the maximal-degree multiplication entries.
Reference: Szegő, Chapter 3; DLMF 18.2.
-/

public section
open MeasureTheory
namespace Polynomial.Sequence

/-- A polynomial of degree n pairs with the nth orthogonal polynomial through
its leading coefficient alone. -/
theorem IsOrthogonal.integralInner_eq_leadingCoeff_div_mul {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    {p : ℝ[X]} {n : ℕ} (hp : p.degree = n) :
    integralInner μ (IntegrablePair.of μ p (P n)) =
      (p.leadingCoeff / (P n).leadingCoeff) * integralInner μ (IntegrablePair.of μ (P n) (P n)) := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hP0 := leadingCoeff_ne_zero.mpr (P.ne_zero n)
  let c := p.leadingCoeff / (P n).leadingCoeff
  have hc : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hp0) hP0
  have hd : (p - c • P n).degree < n := by
    have h := degree_sub_lt_left
      (show p.degree = (c • P n).degree by
        simp [hp, degree_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc)])
      hp0 (show p.leadingCoeff = (c • P n).leadingCoeff by
        rw [leadingCoeff_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc)]
        simp [c, hP0])
    simpa [hp] using h
  have hz := hP.integralInner_eq_zero_of_degree_lt hμ hd
  rw [integralInner_sub_left hμ, integralInner_smul_left (h := hμ.integrable_mul _ _)] at hz
  exact sub_eq_zero.mp hz

/-- Positive leading coefficients force the top-degree pairing to be positive. -/
theorem IsOrthogonal.integralInner_pos_of_degree_eq {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) {p : ℝ[X]} {n : ℕ}
    (hp : p.degree = n) (hlp : 0 < p.leadingCoeff) (hlP : 0 < (P n).leadingCoeff) :
    0 < integralInner μ (IntegrablePair.of μ p (P n)) := by
  rw [hP.integralInner_eq_leadingCoeff_div_mul hμ hp]
  apply mul_pos (div_pos hlp hlP)
  simpa [integralInner_self] using hpos (P n) (P.ne_zero n)

end Polynomial.Sequence
