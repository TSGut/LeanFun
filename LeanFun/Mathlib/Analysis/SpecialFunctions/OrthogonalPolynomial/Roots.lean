/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ChristoffelDarboux
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.Separable

import Mathlib.Analysis.Polynomial.Order

/-!
# Real and simple zeros of orthogonal polynomials

No restriction on the support of the measure is imposed.
References: Szegő, Chapter 3; DLMF 18.2(vi), https://dlmf.nist.gov/18.2#vi.
-/

@[expose] public section

open MeasureTheory UniqueFactorizationMonoid

namespace Polynomial.Sequence

/-- Every irreducible monic factor of an orthogonal polynomial is linear
(Szegő, Chapter 3). -/
theorem IsOrthogonal.natDegree_eq_one_of_mem_normalizedFactors {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ) {f : ℝ[X]}
    (hf : f ∈ normalizedFactors (P n)) : f.natDegree = 1 := by
  classical
  obtain ⟨hi, hm, q, hpq⟩ := (Polynomial.mem_normalizedFactors_iff (P.ne_zero n)).mp hf
  by_contra hdeg
  have hfpos (x : ℝ) : 0 < f.eval x :=
    zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
      (fun _ hr => (hi.not_isRoot_of_natDegree_ne_one hdeg hr).elim)
      (by rw [hm.leadingCoeff]; norm_num)
  have hq : q ≠ 0 := by
    intro h
    exact P.ne_zero n (by rw [hpq, h, mul_zero])
  have hfd : 0 < f.natDegree := by
    exact natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hi)
  have hqd : q.degree < (n : WithBot ℕ) := by
    rw [degree_eq_natDegree hq, ← P.natDegree_eq n, hpq,
      natDegree_mul hi.ne_zero hq]
    exact_mod_cast (show q.natDegree < f.natDegree + q.natDegree by omega)
  have hzero := hP.integralInner_eq_zero_of_degree_lt hμ hqd
  have hsupp : Function.support (fun x => q.eval x * (P n).eval x) =
      Function.support (fun x => q.eval x ^ 2) := by
    ext x
    simp only [Function.mem_support, hpq, eval_mul, ne_eq, mul_eq_zero]
    simp [ne_of_gt (hfpos x)]
  have hpositive : 0 < integralInner μ (IntegrablePair.of μ q (P n)) := by
    apply (integral_pos_iff_support_of_nonneg ?_ (hμ.integrable_mul q (P n))).mpr
    · rw [hsupp]
      exact (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg (q.eval x))
        (hμ q)).mp (hpos q hq)
    · intro x
      change 0 ≤ q.eval x * (P n).eval x
      rw [hpq, eval_mul]
      nlinarith [mul_nonneg (le_of_lt (hfpos x)) (sq_nonneg (q.eval x))]
  exact (ne_of_gt hpositive) hzero

/-- Every orthogonal polynomial splits over the reals (DLMF 18.2(vi)). -/
theorem IsOrthogonal.splits {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (n : ℕ) : (P n).Splits := by
  classical
  rw [← leadingCoeff_mul_prod_normalizedFactors (P n)]
  apply (Splits.C _).mul
  apply Splits.multisetProd
  intro f hf
  exact Splits.of_natDegree_le_one
    (le_of_eq (hP.natDegree_eq_one_of_mem_normalizedFactors hμ hpos n hf))

/-- The degree-`n` member has `n` real roots, counted with multiplicity
(DLMF 18.2(vi)). -/
theorem IsOrthogonal.card_roots {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (n : ℕ) : (P n).roots.card = n := by
  rw [← (hP.splits hμ hpos n).natDegree_eq_card_roots, P.natDegree_eq]

/-- No real root occurs more than once (DLMF 18.2(vi)). -/
theorem IsOrthogonal.roots_nodup {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (n : ℕ) : (P n).roots.Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro x
  rw [count_roots]
  apply Nat.le_of_not_gt
  intro hx
  obtain ⟨hr, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot (P.ne_zero n)).mp hx
  exact hP.derivative_eval_ne_zero hμ hpos n x hr hd

/-- All complex roots are simple as well: the real polynomial is separable
(Szegő, Chapter 3). -/
theorem IsOrthogonal.separable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (n : ℕ) : (P n).Separable :=
  (nodup_roots_iff_of_splits (P.ne_zero n) (hP.splits hμ hpos n)).mp
    (hP.roots_nodup hμ hpos n)

end Polynomial.Sequence
