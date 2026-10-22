/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Uniqueness
public import LeanFun.Mathlib.RingTheory.Polynomial.Reflection
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Parity of orthogonal polynomials for even measures

Reflection invariance and uniqueness force degree parity, independently of the
normalization of the orthogonal sequence. Reference: Szegő, Chapter 3;
Dunkl–Xu, symmetric one-dimensional factors in Cartesian product constructions.
-/

public section
open MeasureTheory
namespace Polynomial.Sequence

/-- Orthogonal polynomials for a nondegenerate even measure have degree parity. -/
theorem IsOrthogonal.comp_neg_X {μ : Measure ℝ} [μ.IsNegInvariant]
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ) :
    (P n).comp (-X) = C ((-1 : ℝ) ^ n) * P n := by
  let Q : Sequence ℝ :=
    { elems' := fun k => (P k).comp (-X)
      degree_eq' := fun k => by
        rw [degree_comp (by simp : 0 < (-X : ℝ[X]).degree)]
        simp [P.degree_eq] }
  have hQ : Q.IsOrthogonal μ := by
    constructor
    · intro m n
      exact hμ.integrable_mul (Q m) (Q n)
    · intro m n hmn
      change (∫ x, ((P m).comp (-X)).eval x * ((P n).comp (-X)).eval x ∂μ) = 0
      simp only [eval_comp, eval_neg, eval_X]
      rw [integral_neg_eq_self (fun x => (P m).eval x * (P n).eval x) μ]
      exact hP.orthogonal m n hmn
  have he := hP.eq_leadingCoeff_div_smul hμ hpos hQ n
  change (P n).comp (-X) =
    (((P n).comp (-X)).leadingCoeff / (P n).leadingCoeff) • P n at he
  rw [leadingCoeff_comp (by simp : (-X : ℝ[X]).natDegree ≠ 0),
    leadingCoeff_neg, leadingCoeff_X, P.natDegree_eq] at he
  have hp := leadingCoeff_ne_zero.mpr (P.ne_zero n)
  have hc : ((P n).leadingCoeff * (-1 : ℝ) ^ n) / (P n).leadingCoeff = (-1 : ℝ) ^ n := by
    field_simp
  rw [hc, smul_eq_C_mul] at he
  exact he

/-- The coefficient version of parity for a general even orthogonality measure. -/
theorem IsOrthogonal.coeff_eq_zero_of_parity {μ : Measure ℝ} [μ.IsNegInvariant]
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n j : ℕ) (hj : j % 2 ≠ n % 2) :
    (P n).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_reflection n j (hP.comp_neg_X hμ hpos n) hj

end Polynomial.Sequence
