/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Existence
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Positive-leading orthonormal polynomial sequences

Every nondegenerate polynomial measure admits the positive normalization used
in Cholesky measure conversion. Reference: Gautschi, *Orthogonal Polynomials*;
Dunkl–Xu, Chapter 3.
-/

@[expose] public section
open MeasureTheory
namespace Polynomial.Sequence

/-- Rescale a degree-indexed sequence by nonzero real constants. -/
noncomputable def rescale (P : Sequence ℝ) (c : ℕ → ℝ) (hc : ∀ n, c n ≠ 0) : Sequence ℝ where
  elems' n := c n • P n
  degree_eq' n := by
    rw [degree_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero (hc n)), P.degree_eq]

@[simp] theorem rescale_apply (P : Sequence ℝ) (c : ℕ → ℝ) (hc : ∀ n, c n ≠ 0) (n : ℕ) :
    P.rescale c hc n = c n • P n := rfl

/-- Nonzero scalar normalization preserves orthogonality. -/
theorem IsOrthogonal.rescale {μ : Measure ℝ} {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (c : ℕ → ℝ) (hc : ∀ n, c n ≠ 0) : (P.rescale c hc).IsOrthogonal μ := by
  constructor
  · intro m n
    have h := (hP.integrable m n).const_mul (c m * c n)
    convert h using 1
    funext x
    simp only [rescale_apply, eval_smul, smul_eq_mul]
    ring
  · intro m n hmn
    simp only [rescale_apply, eval_smul, smul_eq_mul]
    have h (x : ℝ) : c m * (P m).eval x * (c n * (P n).eval x) =
        (c m * c n) * ((P m).eval x * (P n).eval x) := by ring
    simp_rw [h]
    rw [integral_const_mul, hP.orthogonal m n hmn, mul_zero]

end Polynomial.Sequence
namespace Polynomial

/-- Positive-leading orthonormal sequences exist for every measure with finite
moments and a strictly positive polynomial pairing. -/
theorem exists_positive_orthonormal_sequence (μ : Measure ℝ) (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) :
    ∃ P : Sequence ℝ, P.IsOrthogonal μ ∧
      (∀ n, 0 < (P n).leadingCoeff) ∧ (∀ n, ∫ x, (P n).eval x ^ 2 ∂μ = 1) := by
  obtain ⟨R, hR⟩ := exists_isOrthogonal μ hμ hpos
  have hr (n : ℕ) : (R n).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (R.ne_zero n)
  let Q := R.rescale (fun n => (R n).leadingCoeff⁻¹) (fun n => inv_ne_zero (hr n))
  have hQ : Q.IsOrthogonal μ := hR.rescale _ _
  have hlead (n : ℕ) : (Q n).leadingCoeff = 1 := by
    change ((R n).leadingCoeff⁻¹ • R n).leadingCoeff = 1
    rw [leadingCoeff_smul_of_smul_regular _
      (IsSMulRegular.of_ne_zero (inv_ne_zero (hr n))), smul_eq_mul, inv_mul_cancel₀ (hr n)]
  let a (n : ℕ) := Real.sqrt (∫ x, (Q n).eval x ^ 2 ∂μ)
  have ha (n : ℕ) : 0 < a n := Real.sqrt_pos.mpr (hpos (Q n) (Q.ne_zero n))
  let P := Q.rescale (fun n => (a n)⁻¹) (fun n => inv_ne_zero (ha n).ne')
  refine ⟨P, hQ.rescale _ _, ?_, ?_⟩
  · intro n
    change 0 < ((a n)⁻¹ • Q n).leadingCoeff
    rw [leadingCoeff_smul_of_smul_regular _
      (IsSMulRegular.of_ne_zero (inv_ne_zero (ha n).ne')), smul_eq_mul, hlead, mul_one]
    exact inv_pos.mpr (ha n)
  · intro n
    change ∫ x, ((a n)⁻¹ • Q n).eval x ^ 2 ∂μ = 1
    simp only [eval_smul, smul_eq_mul, mul_pow, integral_const_mul]
    have hnorm : a n ^ 2 = ∫ x, (Q n).eval x ^ 2 ∂μ :=
      Real.sq_sqrt (hpos (Q n) (Q.ne_zero n)).le
    rw [← hnorm, ← mul_pow, inv_mul_cancel₀ (ha n).ne', one_pow]

end Polynomial
