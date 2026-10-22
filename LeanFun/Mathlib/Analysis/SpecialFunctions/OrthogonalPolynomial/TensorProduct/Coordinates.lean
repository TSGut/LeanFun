/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.TensorProduct.Positive

/-! # Coordinates in normalized tensor-product degree bases
For normalized factors, the complete finite product basis has identity Gram
matrix and coefficients are the corresponding integral pairings.
Reference: orthogonal projection in product polynomial spaces.
-/

public section
open MeasureTheory Polynomial Module
namespace MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Normalized factors give identity Gram matrix on every complete degree section. -/
theorem integralGram_tensorProductDegreeBasis (μ : σ → Measure ℝ)
    (P : σ → Polynomial.Sequence ℝ) (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i))
    (hP : ∀ i, (P i).IsOrthogonal (μ i))
    (hn : ∀ i n, 0 < Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (P i n) (P i n)))
    (hnorm : ∀ i n, Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (P i n) (P i n)) = 1) (N : ℕ) :
    integralGram (Measure.pi μ)
      (fun i ↦ (tensorProductDegreeBasis μ P hμ hP hn N i : MvPolynomial σ ℝ)) = 1 := by
  classical
  let : ∀ i, IsFiniteMeasure (μ i) := fun i ↦ (hμ i).isFiniteMeasure
  ext i j
  simp only [integralGram, tensorProductDegreeBasis_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact integralInner_tensorProductPolynomial_self μ _ (fun t ↦ (hμ t).integrable_mul _ _) (fun t ↦ hnorm t (i.1 t))
  · rw [ite_eq_right hij]
    apply integralInner_tensorProductPolynomial_eq_zero μ P hP
    intro h
    exact hij (Subtype.ext (Finsupp.ext (fun t ↦ congrFun h t)))

/-- Finite normalized tensor coordinates are exact integral projections. -/
theorem tensorProductDegreeBasis_repr (μ : σ → Measure ℝ)
    (P : σ → Polynomial.Sequence ℝ) (hμ : ∀ i, Polynomial.HasFiniteMoments (μ i))
    (hP : ∀ i, (P i).IsOrthogonal (μ i))
    (hn : ∀ i n, 0 < Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (P i n) (P i n)))
    (hnorm : ∀ i n, Polynomial.integralInner (μ i) (Polynomial.IntegrablePair.of (μ i) (P i n) (P i n)) = 1) (N : ℕ)
    (p : restrictTotalDegree σ ℝ N) (i : {d : σ →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (tensorProductDegreeBasis μ P hμ hP hn N).repr p i =
      integralInner (Measure.pi μ) (IntegrablePair.of (Measure.pi μ) (tensorProductPolynomial (fun t ↦ P t (i.1 t))) p) := by
  classical
  let b := tensorProductDegreeBasis μ P hμ hP hn N
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : σ →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  rw [basis_repr_eq_integralInner _ (hasFiniteMoments_pi μ hμ) _
    (integralGram_tensorProductDegreeBasis μ P hμ hP hn hnorm N)]
  simp only [integralInner, tensorProductDegreeBasis_apply]

end MvPolynomial
