/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Recurrence
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Finite polynomial Galerkin matrices
Positive polynomial energy gives positive definite finite sections on every
linearly independent trial family. Reference: the finite-dimensional energy
argument for conforming Galerkin approximation.
-/

public section
open MeasureTheory Matrix
namespace Polynomial
variable {ι : Type*} [Fintype ι] {μ : Measure ℝ}

/-- The finite coefficient quadratic form is exactly the polynomial energy. -/
theorem integralInner_operator_sum (hμ : HasFiniteMoments μ)
    (L : ℝ[X] →ₗ[ℝ] ℝ[X]) (f : ι → ℝ[X]) (v : ι → ℝ) :
    integralInner μ (IntegrablePair.of μ (L (∑ i, v i • f i)) (∑ i, v i • f i)) =
      v ⬝ᵥ ((Matrix.of (fun i j ↦ integralInner μ (IntegrablePair.of μ (L (f j)) (f i)))) *ᵥ v) := by
  have hsmul (p q : ℝ[X]) (a : ℝ) :=
    integralInner_smul_left μ p q a (h := hμ.integrable_mul p q)
  have hr (p : ℝ[X]) : integralInner μ (IntegrablePair.of μ p (∑ i, v i • f i)) =
      ∑ i, v i*integralInner μ (IntegrablePair.of μ p (f i)) := by
    rw [integralInner_comm, integralInner_sum_left hμ]
    simp only [hsmul]
    congr 1
    funext i
    rw [integralInner_comm]
  rw [hr]
  simp only [map_sum, map_smul, integralInner_sum_left hμ, hsmul,
    dotProduct, mulVec, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A positive symmetric polynomial operator has positive definite Galerkin matrices. -/
theorem posDef_integralInner_operator (hμ : HasFiniteMoments μ)
    (L : ℝ[X] →ₗ[ℝ] ℝ[X]) (f : ι → ℝ[X]) (hf : LinearIndependent ℝ f)
    (hsym : ∀ p q, integralInner μ (IntegrablePair.of μ (L p) q) = integralInner μ (IntegrablePair.of μ (L q) p))
    (hpos : ∀ p, p≠0 → 0 < integralInner μ (IntegrablePair.of μ (L p) p)) :
    Matrix.PosDef (Matrix.of (fun i j ↦ integralInner μ (IntegrablePair.of μ (L (f j)) (f i)))) := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
    intro i j
    exact hsym _ _
  · intro v hv
    have hp : (∑ i, v i • f i)≠0 := by
      intro h
      apply hv
      funext i
      exact (Fintype.linearIndependent_iff.mp hf v h) i
    simpa only [star_trivial, ← integralInner_operator_sum hμ] using hpos _ hp

/-- Finite polynomial synthesis turns the matrix rows into tested residuals. -/
theorem integralInner_operator_sum_apply (hμ : HasFiniteMoments μ)
    (L : ℝ[X] →ₗ[ℝ] ℝ[X]) (f : ι → ℝ[X]) (v : ι → ℝ) (i : ι) :
    integralInner μ (IntegrablePair.of μ (L (∑ j, v j • f j)) (f i)) =
      ((Matrix.of (fun i j ↦ integralInner μ (IntegrablePair.of μ (L (f j)) (f i)))) *ᵥ v) i := by
  have hsmul (p q : ℝ[X]) (a : ℝ) :=
    integralInner_smul_left μ p q a (h := hμ.integrable_mul p q)
  simp only [map_sum, map_smul, integralInner_sum_left hμ, hsmul,
    mulVec, dotProduct, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Polynomial
