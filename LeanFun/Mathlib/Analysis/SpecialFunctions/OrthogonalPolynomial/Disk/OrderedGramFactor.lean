/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.OrderedBasis
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.GramFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.GramFactor
import Mathlib.Tactic.FinCases

/-! # Canonical factors for ordered Cartesian connections
Complete degree sections are ordered by total degree and then inner degree.
A separated modification has a positive upper triangular connection in this
ordering, hence it is the canonical factor. Reference: Cholesky uniqueness and
Cartesian measure modification, Gutleb--Olver--Slevinsky.
-/

@[expose] public section
open MeasureTheory Set Polynomial Module Matrix
namespace MvPolynomial.CartesianDiskSystem
variable {μ ν μ' ν' : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') ν')
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)
    (hx' : ∀ᵐ x ∂μ', x ∈ Icc (-1 : ℝ) 1) (hz' : ∀ᵐ z ∂ν', z ∈ Icc (-1 : ℝ) 1)

/-- The complete finite connection in the fixed degree/inner ordering. -/
noncomputable def orderedConnectionMatrix (N : ℕ) :
    Matrix (Fin (Fintype.card (DiskDegreeIndex N))) (Fin (Fintype.card (DiskDegreeIndex N))) ℝ :=
  (T.orderedDegreeBasis hx' hz' N).toMatrix (S.orderedDegreeBasis hx hz N)

/-- Reindexing leaves the actual integral connection entries unchanged. -/
theorem orderedConnectionMatrix_apply (N : ℕ)
    (i j : Fin (Fintype.card (DiskDegreeIndex N))) :
    S.orderedConnectionMatrix T hx hz hx' hz' N i j =
      S.connectionEntry T
        ((diskDegreeOrder N j).1 0 + (diskDegreeOrder N j).1 1) ((diskDegreeOrder N j).1 1)
        ((diskDegreeOrder N i).1 0 + (diskDegreeOrder N i).1 1) ((diskDegreeOrder N i).1 1) := by
  simp only [orderedConnectionMatrix, orderedDegreeBasis, Basis.toMatrix_apply,
    Basis.reindex_apply, Basis.repr_reindex_apply]
  rw [T.degreeBasis_repr hx' hz']
  simp only [S.degreeBasis_apply]
  exact integralInner_comm _ _ _

/-- The ordered connection still factors the target Gram matrix. -/
theorem integralGram_eq_orderedConnectionMatrix_transpose_mul (N : ℕ) :
    integralGram (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') ν'))
      (fun i ↦ (S.orderedDegreeBasis hx hz N i : MvPolynomial (Fin 2) ℝ)) =
      (S.orderedConnectionMatrix T hx hz hx' hz' N).transpose *
        S.orderedConnectionMatrix T hx hz hx' hz' N := by
  apply integralGram_eq_transpose_toMatrix_mul _
    (hasFiniteMoments_cartesianDiskMeasure hx' hz') (T.hasPositiveDefiniteIntegral hx' hz')
  classical
  ext i j
  simp only [integralGram, orderedDegreeBasis_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    rw [T.integralInner_polynomial_self hx', ite_eq_left rfl]
  · rw [ite_eq_right hij]
    apply T.integralInner_polynomial_eq_zero hx' (by omega) (by omega)
    intro h
    apply hij
    apply (diskDegreeOrder N).injective
    apply DiskDegreeIndex.ext
    have hn := congrArg Prod.fst h
    have hk := congrArg Prod.snd h
    ext t
    fin_cases t <;> dsimp at hn hk ⊢ <;> omega

section Separated
variable [ν.IsNegInvariant]
    (h g : ℝ[X]) (l : ℕ)
    [IsFiniteMeasure (diskOuterModification h l (μ.comap Subtype.val))]
    [IsFiniteMeasure (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val))]
    (U : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))
    (hμ : Polynomial.HasFiniteMoments μ) (hν : Polynomial.HasFiniteMoments ν)
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (hg : ∀ᵐ x ∂ν, 0 ≤ g.eval x)
    (hgpar : ∀ x, g.eval (-x) = g.eval x) (hgdeg : g.natDegree ≤ 2 * l)
    (hzU : ∀ᵐ z ∂Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val), z ∈ Icc (-1 : ℝ) 1)

include hμ hν hh hg

include hgpar hgdeg in
/-- The separated connection is upper triangular in total-degree/inner order. -/
theorem orderedConnectionMatrix_isUpperTriangular (N : ℕ) :
    (S.orderedConnectionMatrix U hx hz (ae_mem_diskOuterModification hx h l) hzU N).IsUpperTriangular := by
  intro i j hij
  rw [orderedConnectionMatrix_apply]
  apply S.connectionEntry_eq_zero_of_outside_band h g l U hμ hν hx hh hg hgpar hgdeg
    (by omega) (by omega)
  rintro ⟨s, r, hs, hr, hn, hk⟩
  have hord := (diskDegreeOrder N).strictMono hij
  rw [diskDegreeIndex_lt_iff] at hord
  dsimp only [id_eq] at hord
  rcases hord with hord | ⟨hord, hi⟩ <;> omega

omit [ν.IsNegInvariant] in
/-- Its diagonal is strictly positive, with no independent sign choices. -/
theorem orderedConnectionMatrix_diag_pos (N : ℕ)
    (i : Fin (Fintype.card (DiskDegreeIndex N))) :
    0 < S.orderedConnectionMatrix U hx hz (ae_mem_diskOuterModification hx h l) hzU N i i := by
  rw [orderedConnectionMatrix_apply]
  exact S.connectionEntry_diag_pos h g l U hμ hν hx hh hg _ _

include hgpar hgdeg in
/-- Matching polynomial pairings identify the separated connection with the
canonical factor, including for an independently defined modified measure. -/
theorem integralGramFactor_eq_orderedConnectionMatrix
    (ω : Measure (Fin 2 → ℝ)) (hω : MvPolynomial.HasFiniteMoments ω)
    (hpω : MvPolynomial.HasPositiveDefiniteIntegral ω)
    (hpair : ∀ p q : MvPolynomial (Fin 2) ℝ, integralInner ω (IntegrablePair.of ω p q) =
      integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
        (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val))) (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
        (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val))) (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))) p q)) (N : ℕ) :
    integralGramFactor ω hω hpω (S.orderedDegreeBasis hx hz N) =
      S.orderedConnectionMatrix U hx hz (ae_mem_diskOuterModification hx h l) hzU N := by
  apply integralGramFactor_eq
  · exact S.orderedConnectionMatrix_isUpperTriangular hx hz h g l U hμ hν hh hg hgpar hgdeg hzU N
  · exact S.orderedConnectionMatrix_diag_pos hx hz h g l U hμ hν hh hg hzU N
  · rw [← S.integralGram_eq_orderedConnectionMatrix_transpose_mul U hx hz
      (ae_mem_diskOuterModification hx h l) hzU N]
    ext i j
    exact hpair _ _

end Separated
end MvPolynomial.CartesianDiskSystem
