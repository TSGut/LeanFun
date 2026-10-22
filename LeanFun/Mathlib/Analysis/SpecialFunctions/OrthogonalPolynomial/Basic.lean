/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Orthogonal polynomial sequences

Orthogonality is a predicate on Mathlib's degree-indexed polynomial sequences.
It imposes integrability and orthogonality, but no normalisation or positivity.

References: DLMF 18.2(i), https://dlmf.nist.gov/18.2; Szegő, *Orthogonal Polynomials*, Chapter 3.
-/

public section

open MeasureTheory

namespace Polynomial.Sequence

/-- A polynomial sequence is orthogonal when its pairwise products are integrable
and distinct elements have zero integral product (DLMF 18.2(i), Szegő, Chapter 3).
Positivity of squared norms is deliberately a separate hypothesis. -/
structure IsOrthogonal (P : Sequence ℝ) (μ : Measure ℝ) : Prop where
  integrable : ∀ m n, Integrable (fun x => (P m).eval x * (P n).eval x) μ
  orthogonal : ∀ m n, m ≠ n → ∫ x, (P m).eval x * (P n).eval x ∂μ = 0

/-- Every polynomial sequence is orthogonal for the zero measure, demonstrating
why uniqueness needs nondegeneracy (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem isOrthogonal_zero (P : Sequence ℝ) : P.IsOrthogonal 0 where
  integrable _ _ := integrable_zero_measure
  orthogonal _ _ _ := integral_zero_measure _

/-- The squared norm of each element of an orthogonal sequence is integrable
(DLMF 18.2(i), Szegő, Chapter 3). -/
theorem IsOrthogonal.integrable_sq {P : Sequence ℝ} {μ : Measure ℝ}
    (hP : P.IsOrthogonal μ) (n : ℕ) : Integrable (fun x => (P n).eval x ^ 2) μ := by
  simpa only [pow_two] using hP.integrable n n

/-- Orthogonality is unchanged by an almost-everywhere identical sequence of
polynomial evaluations (DLMF 18.2(i), Szegő, Chapter 3). -/
theorem IsOrthogonal.congr_ae {P Q : Sequence ℝ} {μ : Measure ℝ}
    (hP : P.IsOrthogonal μ) (h : ∀ n, (fun x => (P n).eval x) =ᵐ[μ] fun x => (Q n).eval x) :
    Q.IsOrthogonal μ where
  integrable m n := (hP.integrable m n).congr ((h m).mul (h n))
  orthogonal m n hmn := by
    have heq : (fun x => (P m).eval x * (P n).eval x) =ᵐ[μ]
        fun x => (Q m).eval x * (Q n).eval x := (h m).mul (h n)
    exact (integral_congr_ae heq).symm.trans (hP.orthogonal m n hmn)

end Polynomial.Sequence
