/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticFullFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticPencil
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.MeasureModification

/-! # Finite even-sector Gram identification for deformed disk measures
The section consists of all even-even indices through degree 2r, with the
highest degree ordered by increasing inner index. Its actual modified Gram
matrix is the concrete affine pencil in the factor nonvanishing theorem.
Reference: Cartesian disk deformation and Cholesky measure modification.
-/

@[expose] public section
open MeasureTheory Set Polynomial Matrix
namespace MvPolynomial

/-- Half-degree coordinates of the leading section and its top degree. -/
def dunklXuEvenBlockCoordinates (r : ℕ) : DunklXuEvenInterior r ⊕ Fin (r + 1) → ℕ × ℕ
  | Sum.inl i => (i.1.1, i.1.2)
  | Sum.inr i => (r - i, i)

/-- Block coordinates enumerate distinct even-even polynomials. -/
theorem dunklXuEvenBlockCoordinates_injective (r : ℕ) :
    Function.Injective (dunklXuEvenBlockCoordinates r) := by
  intro i j h
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      congr 1
      apply Subtype.ext
      exact Prod.ext (Fin.ext ha) (Fin.ext hb)
    | inr j =>
      have hi := i.2
      dsimp [dunklXuEvenBlockCoordinates] at ha hb
      omega
  | inr i =>
    cases j with
    | inl j =>
      have hj := j.2
      dsimp [dunklXuEvenBlockCoordinates] at ha hb
      omega
    | inr j => exact congrArg Sum.inr (Fin.ext hb)

/-- The concrete block pencil has the same entries as the normalized full disk perturbation. -/
theorem dunklXuEvenGramPencil_apply {β : ℝ} (hβ : -1 < β) (u v t : ℝ) (r : ℕ)
    (i j : DunklXuEvenInterior r ⊕ Fin (r + 1)) :
    dunklXuEvenGramPencil hβ u v t r i j = (if i = j then 1 else 0) +
      t * dunklXuQuadraticMatrix hβ u v
        (dunklXuEvenIndex (dunklXuEvenBlockCoordinates r i).1 (dunklXuEvenBlockCoordinates r i).2)
        (dunklXuEvenIndex (dunklXuEvenBlockCoordinates r j).1 (dunklXuEvenBlockCoordinates r j).2) := by
  classical
  cases i <;> cases j <;>
    simp [dunklXuEvenGramPencil, dunklXuInteriorMatrix, dunklXuQuadraticRightBlock,
      dunklXuQuadraticLeftBlock, dunklXuQuadraticBoundaryBlock, dunklXuEvenBoundary,
      dunklXuEvenBlockCoordinates, Matrix.one_apply]

/-- The modified Gram entry of actual deformed Cartesian polynomials equals
the block pencil when the constant boundary value A+B is normalized to one. -/
theorem integralInner_deformed_quadratic_eq_evenGramPencil {β : ℝ} (hβ : -1 < β)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδpos : Polynomial.HasPositiveDefiniteIntegral
      (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val)))
    (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β))
    (A B C : ℝ) (hAB : A + B = 1)
    (hu : ∀ᵐ x ∂cartesianDiskMeasure
      (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (ProductMeasureInput.ofSFinite (hν := by infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β)),
      0 ≤ eval x (coordinateQuadratic A B C))
    (r : ℕ) (i j : DunklXuEvenInterior r ⊕ Fin (r + 1)) :
    let ci := dunklXuEvenBlockCoordinates r i
    let cj := dunklXuEvenBlockCoordinates r j
    integralInner (MvPolynomial.polynomialDensityMeasure ((coordinateQuadratic A B C)) (((cartesianDiskMeasure
      (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val)))
      (ProductMeasureInput.ofSFinite (hν := by infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β)))).comap Subtype.val)) (IntegrablePair.of (MvPolynomial.polynomialDensityMeasure ((coordinateQuadratic A B C)) (((cartesianDiskMeasure
      (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val)))
      (ProductMeasureInput.ofSFinite (hν := by infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β)))).comap Subtype.val)) (T.polynomial (2 * ci.1 + 2 * ci.2) (2 * ci.2)) (T.polynomial (2 * cj.1 + 2 * cj.2) (2 * cj.2)) (h := ((T.hasFiniteMoments (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 (ae_mem_Icc_jacobiMeasure _ _))).withDensity_polynomial _ hu).integrable_mul _ _)) =
        dunklXuEvenGramPencil hβ B C δ r i j := by
  dsimp only
  rw [MvPolynomial.integralInner_withDensity_polynomial _ _ _ hu (hpq := (T.hasFiniteMoments (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 (ae_mem_Icc_jacobiMeasure _ _))).integrable_mul _ _)]
  have he := integral_quadratic_deformed_eq_dunklXu_pencil hβ hδ hδ1 hδpos T
    (dunklXuEvenBlockCoordinates r i).1 (dunklXuEvenBlockCoordinates r i).2
    (dunklXuEvenBlockCoordinates r j).1 (dunklXuEvenBlockCoordinates r j).2 A B C
  rw [hAB, one_mul] at he
  rw [dunklXuEvenGramPencil_apply]
  have hcoord : dunklXuEvenBlockCoordinates r i = dunklXuEvenBlockCoordinates r j ↔ i = j :=
    (dunklXuEvenBlockCoordinates_injective r).eq_iff
  simpa only [integralInner, coordinateQuadratic, map_add, map_mul, map_pow, eval_C, eval_X,
    mul_assoc, Prod.mk.eta, hcoord, dunklXuEvenIndex] using he

end MvPolynomial
