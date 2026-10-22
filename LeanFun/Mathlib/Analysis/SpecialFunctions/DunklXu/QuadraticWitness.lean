/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.PolynomialDensityMeasure

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticAdmissibleFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.EvenSectorEmbedding

/-! # Actual quadratic disk witnesses with arbitrarily distant factor entries
For each degree 2r, an admissible deformed Cartesian measure has a nonzero
canonical factor entry from inner index zero to inner index 2r. The measure may
depend on r; no claim is made here for the fixed original uniform disk.
Reference: the varying-factor quadratic obstruction argument.
-/

@[expose] public section
open MeasureTheory Set Polynomial Module Matrix Filter
open scoped Topology
namespace MvPolynomial

/-- Classical parameter and density data for the deformed quadratic disk measure. -/
structure DunklXuDeformedQuadraticInput (β δ A B C : ℝ) : Prop where
  parameter_nonneg : 0 ≤ δ
  parameter_le_one : δ ≤ 1
  density_nonnegative : ∀ᵐ x ∂(cartesianDiskMeasure
    (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (ProductMeasureInput.ofSFinite (hν := by infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β))), 0 ≤ eval x (coordinateQuadratic A B C)

/-- The usual disk inequalities supply the full classical input. -/
theorem DunklXuDeformedQuadraticInput.of_nonneg (β δ A B C : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A) (hAB : 0 ≤ A+B) (hAC : 0 ≤ A+C) :
    DunklXuDeformedQuadraticInput β δ A B C := by
  let : SFinite (jacobiMeasure β β) := by infer_instance
  refine ⟨hδ,hδ1,?_⟩
  exact ae_coordinateQuadratic_nonneg_cartesianDiskMeasure
    (ae_mem_Icc_diskDeformedMeasure hδ hδ1 (ae_mem_Icc_jacobiMeasure _ _))
    (ae_mem_Icc_jacobiMeasure _ _) A B C hA hAB hAC

/-- The deformed quadratic measure uses a nonnegative density on its classical locus. -/
noncomputable def dunklXuDeformedQuadraticMeasure (β δ A B C : ℝ)
    (_d : DunklXuDeformedQuadraticInput β δ A B C := by
      apply MvPolynomial.DunklXuDeformedQuadraticInput.of_nonneg
      all_goals first | assumption | positivity | linarith) : Measure (Fin 2 → ℝ) :=
  MvPolynomial.polynomialDensityMeasure (coordinateQuadratic A B C)
    ((cartesianDiskMeasure
    (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (ProductMeasureInput.ofSFinite (hν := by infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β))).comap Subtype.val)

/-- The certified measure is determined by its nonnegative density on measurable sets. -/
theorem dunklXuDeformedQuadraticMeasure_apply (β δ A B C : ℝ)
    (d : DunklXuDeformedQuadraticInput β δ A B C)
    {s : Set (Fin 2 → ℝ)} (hs : MeasurableSet s) :
    dunklXuDeformedQuadraticMeasure β δ A B C d s =
      ∫⁻ x : {x : Fin 2 → ℝ // 0 ≤ eval x (coordinateQuadratic A B C)} in Subtype.val ⁻¹' s,
        ENNReal.ofNNReal (NNReal.mk (eval (x : Fin 2 → ℝ) (coordinateQuadratic A B C)) x.property)
        ∂((cartesianDiskMeasure
    (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (ProductMeasureInput.ofSFinite (hν := by infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β))).comap Subtype.val) :=
  MvPolynomial.polynomialDensityMeasure_apply _ _ hs

/-- Complete source degree basis in the fixed degree/inner ordering. -/
noncomputable def dunklXuDeformedDegreeBasis {β δ : ℝ} (hβ : -1 < β)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    Basis (Fin (Fintype.card (DiskDegreeIndex N))) ℝ (restrictTotalDegree (Fin 2) ℝ N) := by
  have hβ' : -1 < β + 1 / 2 := by linarith
  let := isFiniteMeasure_jacobiMeasure hβ' hβ'
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  exact (dunklXuDeformedCartesianSystem hβ hδ hδ1).orderedDegreeBasis
    (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 (ae_mem_Icc_jacobiMeasure _ _))
    (ae_mem_Icc_jacobiMeasure _ _) N

@[simp] theorem dunklXuDeformedDegreeBasis_apply {β δ : ℝ} (hβ : -1 < β)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) (i : Fin (Fintype.card (DiskDegreeIndex N))) :
    (dunklXuDeformedDegreeBasis hβ hδ hδ1 N i : MvPolynomial (Fin 2) ℝ) =
      (dunklXuDeformedCartesianSystem hβ hδ hδ1).polynomial
        ((diskDegreeOrder N i).1 0 + (diskDegreeOrder N i).1 1) ((diskDegreeOrder N i).1 1) := by
  simp [dunklXuDeformedDegreeBasis]

/-- The concrete modified measure has moments and is strictly positive on nonzero polynomials. -/
theorem dunklXuDeformedQuadraticMeasure_admissible {β δ : ℝ} (hβ : -1 < β)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (A B C : ℝ)
    (hA : 0 ≤ A) (hAB : 0 < A + B) (hAC : 0 ≤ A + C) :
    MvPolynomial.HasFiniteMoments (dunklXuDeformedQuadraticMeasure β δ A B C) ∧
      MvPolynomial.HasPositiveDefiniteIntegral (dunklXuDeformedQuadraticMeasure β δ A B C) := by
  simp only [dunklXuDeformedQuadraticMeasure]
  have hβ' : -1 < β + 1 / 2 := by linarith
  let := isFiniteMeasure_jacobiMeasure hβ' hβ'
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  have hx := ae_mem_Icc_diskDeformedMeasure hδ.le hδ1
    (ae_mem_Icc_jacobiMeasure (β + 1 / 2) (β + 1 / 2))
  have hz := ae_mem_Icc_jacobiMeasure β β
  exact ⟨(hasFiniteMoments_cartesianDiskMeasure hx hz).withDensity_polynomial _
    (ae_coordinateQuadratic_nonneg_cartesianDiskMeasure hx hz A B C hA hAB.le hAC),
    (dunklXuDeformedCartesianSystem hβ hδ hδ1).hasPositiveDefiniteIntegral_coordinateQuadratic
      hx hz A B C hA hAB hAC⟩

/-- Each requested degree admits an actual factor with inner gap 2r.
All bases, measures, positivity witnesses and sector embeddings are constructed. -/
theorem exists_integralGramFactor_quadratic_distant_entry {β : ℝ} (hβ : -1 < β)
    (A B C : ℝ) (hA : 0 ≤ A) (hAB : 0 < A + B) (hAC : 0 ≤ A + C) (hC : C ≠ 0)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      ∃ (hM : MvPolynomial.HasFiniteMoments (dunklXuDeformedQuadraticMeasure β δ A B C))
        (hP : MvPolynomial.HasPositiveDefiniteIntegral (dunklXuDeformedQuadraticMeasure β δ A B C)),
      integralGramFactor (dunklXuDeformedQuadraticMeasure β δ A B C) hM hP
        (dunklXuDeformedDegreeBasis hβ hδ hδ1 (2 * r))
        (dunklXuEvenSectorEmbedding r (Sum.inr 0))
        (dunklXuEvenSectorEmbedding r (Sum.inr (Fin.last r))) ≠ 0 := by
  have he := eventually_integralGramFactor_admissible_quadratic_ne_zero
    hβ A B C hA hAB hAC hC r hr
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhdsWithin_iff.mp he
  let δ := min ε 1 / 2
  have hδ : 0 < δ := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith [min_le_right ε 1]
  have hδε : δ < ε := by dsimp [δ]; linarith [min_le_left ε 1]
  have ht := he (show δ ∈ Metric.ball 0 ε ∩ ({0}ᶜ : Set ℝ) from
    ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hδ] using hδε,
      by simpa using hδ.ne'⟩)
  obtain ⟨hM, hP⟩ := dunklXuDeformedQuadraticMeasure_admissible hβ hδ hδ1 A B C hA hAB hAC
  refine ⟨δ, hδ, hδ1, hM, hP, ?_⟩
  simp only [dunklXuDeformedQuadraticMeasure] at hM hP ⊢
  refine ht hδ hδ1 (dunklXuDeformedCartesianSystem hβ hδ hδ1) hM hP
    (dunklXuDeformedDegreeBasis hβ hδ hδ1 (2 * r))
    (fun i ↦ (diskDegreeOrder (2 * r) i).1 0 + (diskDegreeOrder (2 * r) i).1 1)
    (fun i ↦ (diskDegreeOrder (2 * r) i).1 1)
    (fun i ↦ dunklXuDeformedDegreeBasis_apply hβ hδ hδ1 (2 * r) i)
    (dunklXuEvenSectorEmbedding r) (dunklXuEvenSectorEmbedding_injective r) ?_ ?_
    (dunklXuEvenSectorEmbedding_before r) (dunklXuEvenSectorEmbedding_strictMono r)
  · intro i
    simp [diskDegreeOrder_evenSectorEmbedding]
  · intro i h0 h1
    apply dunklXuEvenSectorEmbedding_covers r i _ h1
    simpa using h0

end MvPolynomial
