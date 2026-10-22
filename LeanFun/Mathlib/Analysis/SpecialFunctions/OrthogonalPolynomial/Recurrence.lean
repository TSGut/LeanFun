/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Uniqueness

/-!
# Multiplication by the variable in an orthogonal polynomial basis

The integral pairing makes multiplication by `X` symmetric. Orthogonality to
lower-degree polynomials then forces all matrix entries beyond adjacent indices to vanish.

References: DLMF 18.2(iv), https://dlmf.nist.gov/18.2#iv; Szegő, *Orthogonal Polynomials*, Chapter 3.
-/

public section

open MeasureTheory

namespace Polynomial

/-- Multiplication by the variable is symmetric for the polynomial integral pairing
(DLMF 18.2(iv), Szegő, Chapter 3). -/
theorem integralInner_X_mul (μ : Measure ℝ) (p q : ℝ[X])
    {h : Integrable (fun x => (X * p).eval x * q.eval x) μ} :
    integralInner μ (IntegrablePair.of μ (X * p) q) = integralInner μ (IntegrablePair.of μ p (X * q) (h := by
      convert h using 1
      ext x
      simp only [eval_mul, eval_X]
      ring)) := by
  unfold integralInner
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [eval_mul, eval_X]
  ring

/-- Finite sums pass through the polynomial integral pairing
(DLMF 18.2(i), Szegő, Chapter 3). -/
theorem integralInner_sum_left {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (q : ℝ[X]) :
    integralInner μ (IntegrablePair.of μ (∑ i ∈ s, f i) q) = ∑ i ∈ s, integralInner μ (IntegrablePair.of μ (f i) q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, integralInner_add_left hμ, ih]

namespace Sequence

/-- Entries of multiplication by `X` vanish outside the three central diagonals
(DLMF 18.2(iv), Szegő, Chapter 3). -/
theorem IsOrthogonal.integralInner_X_mul_eq_zero {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    {m n : ℕ} (hmn : n + 1 < m ∨ m + 1 < n) : integralInner μ (IntegrablePair.of μ (X * P n) (P m)) = 0 := by
  rcases hmn with h | h
  · apply hP.integralInner_eq_zero_of_degree_lt hμ
    simpa [degree_mul, Nat.cast_add, add_comm] using (Nat.cast_lt (α := WithBot ℕ)).2 h
  · rw [integralInner_X_mul, integralInner_comm]
    apply hP.integralInner_eq_zero_of_degree_lt hμ
    simpa [degree_mul, Nat.cast_add, add_comm] using (Nat.cast_lt (α := WithBot ℕ)).2 h

/-- Coordinates in an orthogonal polynomial basis are integral projections
(DLMF 18.2(i), Szegő, Chapter 3). -/
theorem IsOrthogonal.integralInner_eq_basis_repr_mul {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (hu : ∀ i, IsUnit (P i).leadingCoeff) (p : ℝ[X]) (n : ℕ) :
    integralInner μ (IntegrablePair.of μ p (P n)) = (P.basis hu).repr p n * integralInner μ (IntegrablePair.of μ (P n) (P n)) := by
  classical
  let b := P.basis hu
  have hb (i : ℕ) : b i = P i := P.basis_eq_self hu i
  have hsum : (∑ i ∈ (b.repr p).support, b.repr p i • b i) = p := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr p
  have h := congrArg (fun q => integralInner μ (IntegrablePair.of μ q (P n))) hsum
  rw [integralInner_sum_left hμ] at h
  have hsmul (p q : ℝ[X]) (a : ℝ) :=
    integralInner_smul_left μ p q a (h := hμ.integrable_mul p q)
  simp only [hsmul, hb] at h
  have hs : (∑ i ∈ (b.repr p).support,
      b.repr p i * integralInner μ (IntegrablePair.of μ (P i) (P n))) =
      b.repr p n * integralInner μ (IntegrablePair.of μ (P n) (P n)) := by
    apply Finset.sum_eq_single n
    · intro i _ hi
      rw [show integralInner μ (IntegrablePair.of μ (P i) (P n)) = 0 from hP.orthogonal i n hi, mul_zero]
    · intro hn
      rw [Finsupp.notMem_support_iff.mp hn, zero_mul]
  exact h.symm.trans hs

/-- Coordinates are the integral projection divided by the squared norm
(DLMF 18.2(i), Szegő, Chapter 3). -/
theorem IsOrthogonal.basis_repr_eq_integralInner_div {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (hu : ∀ i, IsUnit (P i).leadingCoeff)
    (p : ℝ[X]) (n : ℕ) :
    (P.basis hu).repr p n = integralInner μ (IntegrablePair.of μ p (P n)) / integralInner μ (IntegrablePair.of μ (P n) (P n)) := by
  apply (eq_div_iff (ne_of_gt (show 0 < integralInner μ (IntegrablePair.of μ (P n) (P n)) by
    simpa [integralInner_self] using hpos (P n) (P.ne_zero n)))).2
  exact (hP.integralInner_eq_basis_repr_mul hμ hu p n).symm

/-- Matrix coordinates of multiplication vanish away from adjacent indices
(DLMF 18.2(iv), Szegő, Chapter 3). -/
theorem IsOrthogonal.basis_repr_X_mul_eq_zero {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (hu : ∀ i, IsUnit (P i).leadingCoeff)
    {m n : ℕ} (hmn : n + 1 < m ∨ m + 1 < n) : (P.basis hu).repr (X * P n) m = 0 := by
  have hz := hP.integralInner_X_mul_eq_zero hμ hmn
  rw [hP.integralInner_eq_basis_repr_mul hμ hu] at hz
  apply (mul_eq_zero.mp hz).resolve_right
  exact ne_of_gt (by simpa [integralInner_self] using hpos (P m) (P.ne_zero m))

/-- Every positive-index multiplication has a three-term expansion
(DLMF 18.2(iv), Szegő, Chapter 3). -/
theorem IsOrthogonal.exists_three_term {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ) :
    ∃ a b c : ℝ, X * P (n + 1) = a • P (n + 2) + b • P (n + 1) + c • P n := by
  classical
  let hu (i : ℕ) : IsUnit (P i).leadingCoeff :=
    P.isUnit_leadingCoeff i
  let B := P.basis hu
  have hb (i : ℕ) : B i = P i := P.basis_eq_self hu i
  refine ⟨B.repr (X * P (n + 1)) (n + 2), B.repr (X * P (n + 1)) (n + 1),
    B.repr (X * P (n + 1)) n, ?_⟩
  rw [← hb (n + 2), ← hb (n + 1), ← hb n]
  apply B.repr.injective
  ext k
  by_cases h2 : k = n + 2
  · subst k; simp
  by_cases h1 : k = n + 1
  · subst k; simp
  by_cases h0 : k = n
  · subst k; simp
  have hz : B.repr (X * B (n + 1)) k = 0 := by
    rw [hb]
    exact hP.basis_repr_X_mul_eq_zero hμ hpos hu (by omega)
  simp [h0, h1, h2, hz]

/-- At index zero, multiplication has only the two available terms
(DLMF 18.2(iv), Szegő, Chapter 3). -/
theorem IsOrthogonal.exists_two_term_zero {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) :
    ∃ a b : ℝ, X * P 0 = a • P 1 + b • P 0 := by
  classical
  let hu (i : ℕ) : IsUnit (P i).leadingCoeff :=
    P.isUnit_leadingCoeff i
  let B := P.basis hu
  have hb (i : ℕ) : B i = P i := P.basis_eq_self hu i
  refine ⟨B.repr (X * P 0) 1, B.repr (X * P 0) 0, ?_⟩
  rw [← hb 1, ← hb 0]
  apply B.repr.injective
  ext k
  by_cases h1 : k = 1
  · subst k; simp
  by_cases h0 : k = 0
  · subst k; simp
  have hz : B.repr (X * B 0) k = 0 := by
    rw [hb]
    exact hP.basis_repr_X_mul_eq_zero hμ hpos hu (by omega)
  simp [h0, h1, hz]

end Sequence
end Polynomial
