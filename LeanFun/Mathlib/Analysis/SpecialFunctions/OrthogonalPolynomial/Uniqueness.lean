/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.InnerProduct

import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Uniqueness up to scaling of orthogonal polynomial sequences

Exact degrees turn pairwise orthogonality into orthogonality to all lower-degree
polynomials. Positive definiteness then gives uniqueness up to nonzero scalar factors.

References: DLMF 18.2(i), https://dlmf.nist.gov/18.2; Szegő, *Orthogonal Polynomials*, Chapter 3.
-/

public section

open MeasureTheory Submodule

namespace Polynomial.Sequence

/-- A sequence element is orthogonal to every polynomial of lower degree
(DLMF 18.2(i), Szegő, Chapter 3). -/
theorem IsOrthogonal.integralInner_eq_zero_of_degree_lt {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    {p : ℝ[X]} {n : ℕ} (hp : p.degree < n) : integralInner μ (IntegrablePair.of μ p (P n)) = 0 := by
  have hm : p ∈ span ℝ (P '' Set.Iio n) := by
    rw [P.span_degreeLT (fun i _ =>
      P.isUnit_leadingCoeff i), mem_degreeLT]
    exact hp
  clear hp
  induction hm using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨m, hm, rfl⟩ := hq
    exact hP.orthogonal m n (ne_of_lt hm)
  | zero => exact integralInner_zero_left μ (P n)
  | add p q _ _ hp hq => rw [integralInner_add_left hμ, hp, hq, add_zero]
  | smul a p _ hp =>
    rw [integralInner_smul_left (h := hμ.integrable_mul p (P n)), hp, mul_zero]

/-- At each index, two orthogonal sequences differ by the ratio of their leading
coefficients (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem IsOrthogonal.eq_leadingCoeff_div_smul {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P Q : Sequence ℝ} (hP : P.IsOrthogonal μ) (hQ : Q.IsOrthogonal μ) (n : ℕ) :
    Q n = ((Q n).leadingCoeff / (P n).leadingCoeff) • P n := by
  let c : ℝ := (Q n).leadingCoeff / (P n).leadingCoeff
  have hP0 := leadingCoeff_ne_zero.mpr (P.ne_zero n)
  have hQ0 := leadingCoeff_ne_zero.mpr (Q.ne_zero n)
  have hc : c ≠ 0 := div_ne_zero hQ0 hP0
  have hdeg : (Q n - c • P n).degree < n := by
    have h := degree_sub_lt_left
      (show (Q n).degree = (c • P n).degree by
        simp [degree_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc)])
      (Q.ne_zero n) (show (Q n).leadingCoeff = (c • P n).leadingCoeff by
        rw [leadingCoeff_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc)]
        simp [c, hP0])
    simpa using h
  have hq := hQ.integralInner_eq_zero_of_degree_lt hμ hdeg
  have hp := hP.integralInner_eq_zero_of_degree_lt hμ hdeg
  have hzero : integralInner μ (IntegrablePair.of μ (Q n - c • P n) (Q n - c • P n)) = 0 := by
    rw [integralInner_sub_left hμ, integralInner_smul_left,
      integralInner_comm μ (Q n), integralInner_comm μ (P n), hq, hp]
    all_goals first | exact hμ.integrable_mul _ _ | ring
  exact sub_eq_zero.mp (hpos.eq_zero_of_integralInner_self_eq_zero hzero)

/-- Orthogonal polynomial sequences for the same nondegenerate measure are unique
up to nonzero scalar factors (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem IsOrthogonal.exists_smul {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P Q : Sequence ℝ}
    (hP : P.IsOrthogonal μ) (hQ : Q.IsOrthogonal μ) :
    ∃ c : ℕ → ℝ, (∀ n, c n ≠ 0) ∧ ∀ n, Q n = c n • P n := by
  refine ⟨fun n => (Q n).leadingCoeff / (P n).leadingCoeff, ?_, ?_⟩
  · intro n
    exact div_ne_zero (leadingCoeff_ne_zero.mpr (Q.ne_zero n))
      (leadingCoeff_ne_zero.mpr (P.ne_zero n))
  · exact hP.eq_leadingCoeff_div_smul hμ hpos hQ

end Polynomial.Sequence
