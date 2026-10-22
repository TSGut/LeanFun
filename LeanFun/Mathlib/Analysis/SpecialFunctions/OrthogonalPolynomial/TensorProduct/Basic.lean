/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.InnerProduct
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.InnerProduct
public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskLift
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Tensor products of univariate orthogonal polynomials
Coordinate products are actual multivariate polynomials. Their pairings factor
for finite products of measures, without interval assumptions.
Reference: Dunkl--Xu, product orthogonal polynomials.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace MvPolynomial
variable {σ : Type*} [Fintype σ]

/-- Embed each univariate factor in its own coordinate and multiply. -/
noncomputable def tensorProductPolynomial (p : σ → ℝ[X]) : MvPolynomial σ ℝ :=
  ∏ i, (p i).eval₂ C (X i)

/-- Evaluation is the pointwise product of the univariate evaluations. -/
@[simp] theorem eval_tensorProductPolynomial (p : σ → ℝ[X]) (x : σ → ℝ) :
    eval x (tensorProductPolynomial p) = ∏ i, (p i).eval (x i) := by
  simp [tensorProductPolynomial, eval_eval₂_C_X]

/-- Tensor product degree is bounded by the sum of the factor degrees. -/
theorem totalDegree_tensorProductPolynomial_le (p : σ → ℝ[X]) :
    (tensorProductPolynomial p).totalDegree ≤ ∑ i, (p i).natDegree := by
  classical
  have h (s : Finset σ) : (∏ i ∈ s, (p i).eval₂ C (X i)).totalDegree ≤
      ∑ i ∈ s, (p i).natDegree := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (totalDegree_mul _ _).trans (Nat.add_le_add (totalDegree_eval₂_C_X_le (p i) i) hs)
  exact h Finset.univ

/-- Products of coordinate-integrable polynomial pairs are integrable. -/
theorem integrable_mul_tensorProductPolynomial (μ : σ → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (p q : σ → ℝ[X])
    (h : ∀ i, Integrable (fun x => (p i).eval x * (q i).eval x) (μ i)) :
    Integrable (fun x => eval x (tensorProductPolynomial p) *
      eval x (tensorProductPolynomial q)) (Measure.pi μ) := by
  simpa only [eval_tensorProductPolynomial, ← Finset.prod_mul_distrib] using
    Integrable.fintype_prod h

/-- Product-measure pairings factor into their coordinate pairings. -/
theorem integralInner_tensorProductPolynomial (μ : σ → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (p q : σ → ℝ[X])
    (h : ∀ i, Integrable (fun x => (p i).eval x * (q i).eval x) (μ i) := by
      intro i
      solve_by_elim (maxDepth := 4) [Polynomial.HasFiniteMoments.integrable_mul,
        Polynomial.Sequence.IsOrthogonal.integrable]) :
    integralInner (Measure.pi μ) (IntegrablePair.of (Measure.pi μ) (tensorProductPolynomial p) (tensorProductPolynomial q)
      (h := integrable_mul_tensorProductPolynomial μ p q h)) =
      ∏ i, Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (p i) (q i)) := by
  simp only [integralInner, eval_tensorProductPolynomial, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i x ↦ (p i).eval x * (q i).eval x)

/-- Distinct multiindices give orthogonal tensor products of orthogonal sequences. -/
theorem integralInner_tensorProductPolynomial_eq_zero (μ : σ → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (P : σ → Polynomial.Sequence ℝ)
    (hP : ∀ i, (P i).IsOrthogonal (μ i)) (n m : σ → ℕ) (hnm : n ≠ m) :
    integralInner (Measure.pi μ) (IntegrablePair.of (Measure.pi μ) (tensorProductPolynomial (fun i ↦ P i (n i))) (tensorProductPolynomial (fun i ↦ P i (m i)))
      (h := integrable_mul_tensorProductPolynomial μ _ _ (fun i => (hP i).integrable _ _))) = 0 := by
  classical
  rw [integralInner_tensorProductPolynomial μ _ _ (fun i => (hP i).integrable _ _)]
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ m i := by
    by_contra h
    apply hnm
    funext i
    simpa using not_exists.mp h i
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact (hP i).orthogonal (n i) (m i) hi

/-- Tensor products of normalized factors are normalized. -/
theorem integralInner_tensorProductPolynomial_self (μ : σ → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (p : σ → ℝ[X])
    (hi : ∀ i, Integrable (fun x => (p i).eval x * (p i).eval x) (μ i))
    (hp : ∀ i, Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (p i) (p i)) = 1) :
    integralInner (Measure.pi μ) (IntegrablePair.of (Measure.pi μ) (tensorProductPolynomial p) (tensorProductPolynomial p)
      (h := integrable_mul_tensorProductPolynomial μ _ _ hi)) = 1 := by
  rw [integralInner_tensorProductPolynomial μ p p hi]
  simp [hp]

end MvPolynomial
