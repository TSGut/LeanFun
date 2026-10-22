/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.TensorProduct.Positive
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionSupport
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.MeasureModification

/-! # Separated measure modification of tensor products
Actual multivariate polynomial-density pairings factor into one-dimensional
modified pairings. The connection support is a coordinatewise finite box.
Reference: Gutleb--Olver--Slevinsky and tensor-product measure conversion.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial
variable {σ : Type*} [Fintype σ]

/-- Tensor products preserve coordinatewise polynomial multiplication. -/
theorem tensorProductPolynomial_mul (p q : σ → ℝ[X]) :
    tensorProductPolynomial (fun i ↦ p i * q i) =
      tensorProductPolynomial p * tensorProductPolynomial q := by
  simp only [tensorProductPolynomial, Polynomial.eval₂_mul, Finset.prod_mul_distrib]

/-- A separated polynomial density gives the product of the modified factor pairings. -/
theorem integralInner_tensorProductModification (μ : σ → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (h p q : σ → ℝ[X])
    (hh : ∀ i, ∀ᵐ x ∂μ i, 0 ≤ (h i).eval x)
    (hu : ∀ᵐ x ∂Measure.pi μ, 0 ≤ eval x (tensorProductPolynomial h))
    (hi : ∀ i, Integrable (fun x => (h i*p i).eval x*(q i).eval x) (μ i) := by
      intro i
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (MvPolynomial.polynomialDensityMeasure ((tensorProductPolynomial h)) (((Measure.pi μ)).comap Subtype.val)) (IntegrablePair.of (MvPolynomial.polynomialDensityMeasure ((tensorProductPolynomial h)) (((Measure.pi μ)).comap Subtype.val)) (tensorProductPolynomial p) (tensorProductPolynomial q) (h := (MvPolynomial.integrable_mul_withDensity_polynomial_iff _ _ _ hu).2 (by simpa only [tensorProductPolynomial_mul] using integrable_mul_tensorProductPolynomial μ (fun i => h i*p i) q hi))) =
      ∏ i, Polynomial.integralInner (Polynomial.polynomialDensityMeasure ((h i)) (((μ i)).comap Subtype.val)) (Polynomial.IntegrablePair.of (Polynomial.polynomialDensityMeasure ((h i)) (((μ i)).comap Subtype.val)) (p i) (q i) (h := (Polynomial.integrable_polynomialDensityMeasure_comap_mul_iff (h i) (p i) (q i) (hh i)).2 (hi i))) := by
  have hpq : Integrable (fun x => eval x (tensorProductPolynomial h*tensorProductPolynomial p)*eval x (tensorProductPolynomial q)) (Measure.pi μ) := by
    simpa only [tensorProductPolynomial_mul] using
      integrable_mul_tensorProductPolynomial μ (fun i => h i*p i) q hi
  rw [MvPolynomial.integralInner_withDensity_polynomial _ _ _ hu (hpq := hpq)]
  simp only [← tensorProductPolynomial_mul]
  rw [integralInner_tensorProductPolynomial μ (fun i => h i*p i) q (h := hi)]
  apply Finset.prod_congr rfl
  intro i _
  exact (Polynomial.integralInner_polynomialDensityMeasure_comap (h i) (p i) (q i) (hh i)
    (hpq := hi i)).symm

/-- Leaving the univariate modification band in any coordinate makes the
multivariate connection coefficient exactly zero. -/
theorem integralInner_tensorProductModification_eq_zero_of_gap (μ : σ → Measure ℝ)
    (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i)) (h : σ → ℝ[X])
    (hh : ∀ i, ∀ᵐ x ∂μ i, 0 ≤ (h i).eval x)
    (hu : ∀ᵐ x ∂Measure.pi μ, 0 ≤ eval x (tensorProductPolynomial h))
    (P Q : σ → Polynomial.Sequence ℝ)
    (hP : ∀ i, (P i).IsOrthogonal (μ i))
    (hQ : ∀ i, (Q i).IsOrthogonal (Polynomial.polynomialDensityMeasure ((h i)) (((μ i)).comap Subtype.val)))
    (n m : σ → ℕ) (i : σ) (hgap : n i < m i ∨ m i + (h i).natDegree < n i) :
    integralInner (MvPolynomial.polynomialDensityMeasure ((tensorProductPolynomial h)) (((Measure.pi μ)).comap Subtype.val)) (IntegrablePair.of (MvPolynomial.polynomialDensityMeasure ((tensorProductPolynomial h)) (((Measure.pi μ)).comap Subtype.val)) (tensorProductPolynomial (fun j ↦ P j (n j))) (tensorProductPolynomial (fun j ↦ Q j (m j)))) = 0 := by
  let : ∀ i, IsFiniteMeasure (μ i) := fun i ↦ (hμ i).isFiniteMeasure
  rw [integralInner_tensorProductModification μ h _ _ hh hu]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact (hP i).integralInner_eq_zero_of_polynomial_modification (hμ i) (h i) (hh i) (hQ i) hgap

end MvPolynomial
