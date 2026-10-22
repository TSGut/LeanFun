/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticWitness
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticCofiniteAdmissible
public import LeanFun.Mathlib.Analysis.Real.CofiniteChoice
/-! # A single deformation with unbounded quadratic inner fill
For each degree only finitely many parameters are exceptional. One positive
parameter outside the countable union gives every distant entry simultaneously.
This does not identify the original uniform disk, nor an explicit rational parameter.
Reference: rational matrix pencils and the varying-measure quadratic obstruction.
-/

public section
open MeasureTheory Set Polynomial Module Matrix Filter
namespace MvPolynomial

/-- Each complete degree section has only finitely many exceptional deformations. -/
theorem eventually_cofinite_integralGramFactor_quadratic_distant_entry {β : ℝ} (hβ : -1 < β)
    (A B C : ℝ) (hA : 0 ≤ A) (hAB : 0 < A + B) (hAC : 0 ≤ A + C) (hC : C ≠ 0)
    (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ δ : ℝ in Filter.cofinite, ∀ (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      ∃ (hM : MvPolynomial.HasFiniteMoments (dunklXuDeformedQuadraticMeasure β δ A B C))
        (hP : MvPolynomial.HasPositiveDefiniteIntegral (dunklXuDeformedQuadraticMeasure β δ A B C)),
      integralGramFactor (dunklXuDeformedQuadraticMeasure β δ A B C) hM hP
        (dunklXuDeformedDegreeBasis hβ hδ hδ1 (2 * r))
        (dunklXuEvenSectorEmbedding r (Sum.inr 0))
        (dunklXuEvenSectorEmbedding r (Sum.inr (Fin.last r))) ≠ 0 := by
  filter_upwards [eventually_cofinite_integralGramFactor_admissible_quadratic_ne_zero
    hβ A B C hA hAB hAC hC r hr] with δ ht
  intro hδ hδ1
  obtain ⟨hM, hP⟩ := dunklXuDeformedQuadraticMeasure_admissible hβ hδ hδ1 A B C hA hAB hAC
  refine ⟨hM, hP, ?_⟩
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

/-- One actual admissible deformation has all the arbitrarily distant entries.
The same measure is used for every r; its parameter is not prescribed. -/
theorem exists_fixed_deformation_integralGramFactor_all_distant_entries {β : ℝ} (hβ : -1 < β)
    (A B C : ℝ) (hA : 0 ≤ A) (hAB : 0 < A + B) (hAC : 0 ≤ A + C) (hC : C ≠ 0)
    :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1), ∀ (r : ℕ), 2 ≤ r →
      ∃ (hM : MvPolynomial.HasFiniteMoments (dunklXuDeformedQuadraticMeasure β δ A B C))
        (hP : MvPolynomial.HasPositiveDefiniteIntegral (dunklXuDeformedQuadraticMeasure β δ A B C)),
      integralGramFactor (dunklXuDeformedQuadraticMeasure β δ A B C) hM hP
        (dunklXuDeformedDegreeBasis hβ hδ hδ1 (2 * r))
        (dunklXuEvenSectorEmbedding r (Sum.inr 0))
        (dunklXuEvenSectorEmbedding r (Sum.inr (Fin.last r))) ≠ 0 := by
  have h := fun r : {r : ℕ // 2 ≤ r} ↦
    eventually_cofinite_integralGramFactor_quadratic_distant_entry
      hβ A B C hA hAB hAC hC r.1 r.2
  obtain ⟨δ, hδ, hall⟩ := Real.exists_Ioo_forall_of_eventually_cofinite _ h
    (a := 0) (b := 1) (by norm_num)
  exact ⟨δ, hδ.1, hδ.2.le, fun r hr ↦ hall ⟨r, hr⟩ hδ.1 hδ.2.le⟩

end MvPolynomial
