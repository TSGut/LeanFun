/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.TensorProduct.Moments
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Recurrence
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-! # Coordinate multiplication on tensor-product polynomials
Each coordinate operator changes only that coordinate's polynomial degree and
has the same three-diagonal support as the univariate operator.
Reference: tensor-product Jacobi matrices.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Updating one factor leaves the product of all the other factors unchanged. -/
theorem tensorProductPolynomial_update (p : σ → ℝ[X]) (i : σ) (q : ℝ[X]) :
    tensorProductPolynomial (Function.update p i q) =
      q.eval₂ C (X i) * ∏ j ∈ Finset.univ.erase i, (p j).eval₂ C (X j) := by
  unfold tensorProductPolynomial
  have he : (fun j ↦ (Function.update p i q j).eval₂ C (X j)) =
      Function.update (fun j ↦ (p j).eval₂ C (X j)) i (q.eval₂ C (X i)) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [show (Finset.univ \ {i} : Finset σ) = Finset.univ.erase i by
    ext j
    simp [ne_comm]]

/-- Multiplication by one coordinate is exactly multiplication in that factor. -/
theorem X_mul_tensorProductPolynomial (p : σ → ℝ[X]) (i : σ) :
    X i * tensorProductPolynomial p =
      tensorProductPolynomial (Function.update p i (Polynomial.X * p i)) := by
  have hp := tensorProductPolynomial_update p i (p i)
  rw [Function.update_eq_self] at hp
  rw [hp, tensorProductPolynomial_update]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X]
  ring

/-- The coordinate-multiplication pairing is the product of its univariate pairings. -/
theorem integralInner_X_mul_tensorProductPolynomial (μ : σ → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (p q : σ → ℝ[X]) (i : σ)
    (hi : ∀ j, Integrable (fun x =>
      (Function.update p i (Polynomial.X * p i) j).eval x * (q j).eval x) (μ j) := by
      intro j
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (Measure.pi μ) (IntegrablePair.of (Measure.pi μ) (X i * tensorProductPolynomial p) (tensorProductPolynomial q) (h := by
      rw [X_mul_tensorProductPolynomial]
      exact integrable_mul_tensorProductPolynomial μ _ _ hi)) =
      ∏ j, Polynomial.integralInner (μ j) (Polynomial.IntegrablePair.of (μ j) (Function.update p i (Polynomial.X * p i) j) (q j)) := by
  simpa only [integralInner, IntegrablePair.of, X_mul_tensorProductPolynomial] using
    integralInner_tensorProductPolynomial μ (Function.update p i (Polynomial.X * p i)) q hi

/-- A coordinate operator cannot change any other coordinate degree. -/
theorem integralInner_X_mul_tensorProductPolynomial_eq_zero_of_other_index
    (μ : σ → Measure ℝ) [∀ i, SigmaFinite (μ i)] (P : σ → Polynomial.Sequence ℝ)
    (hP : ∀ i, (P i).IsOrthogonal (μ i)) (n m : σ → ℕ) (i j : σ)
    (hji : j ≠ i) (hnm : n j ≠ m j) :
    integralInner (Measure.pi μ) (IntegrablePair.of (Measure.pi μ) (X i * tensorProductPolynomial (fun k ↦ P k (n k))) (tensorProductPolynomial (fun k ↦ P k (m k)))) = 0 := by
  rw [integralInner_X_mul_tensorProductPolynomial μ]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp only [Polynomial.integralInner, Function.update_of_ne hji]
  exact (hP j).orthogonal (n j) (m j) hnm

/-- In its own coordinate, multiplication has only the three central diagonals. -/
theorem integralInner_X_mul_tensorProductPolynomial_eq_zero_of_gap
    (μ : σ → Measure ℝ) [∀ i, SigmaFinite (μ i)] (P : σ → Polynomial.Sequence ℝ)
    (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i))
    (hP : ∀ i, (P i).IsOrthogonal (μ i)) (n m : σ → ℕ) (i : σ)
    (hgap : n i + 1 < m i ∨ m i + 1 < n i) :
    integralInner (Measure.pi μ) (IntegrablePair.of (Measure.pi μ) (X i * tensorProductPolynomial (fun k ↦ P k (n k))) (tensorProductPolynomial (fun k ↦ P k (m k)))) = 0 := by
  rw [integralInner_X_mul_tensorProductPolynomial μ]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [Polynomial.integralInner, Polynomial.IntegrablePair.of, Function.update_self] using
    (hP i).integralInner_X_mul_eq_zero (hμ i) hgap

end MvPolynomial
