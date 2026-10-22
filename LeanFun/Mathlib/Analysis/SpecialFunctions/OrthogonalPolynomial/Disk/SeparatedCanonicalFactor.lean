/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.OrderedGramFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.ModifiedSystem
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.ModificationDensity
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.MeasureModification

/-! # Inner bandwidth of canonical factors for separated densities
This identifies actual polynomial-density Gram factors with the positive ordered
Cartesian connection. Reference: Gutleb--Olver--Slevinsky, measure modification.
-/

public section
open MeasureTheory Set Polynomial Module Matrix
namespace MvPolynomial.CartesianDiskSystem
variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ν.IsNegInvariant]

/-- Separated polynomial modification bounds both directions of the canonical
factor's inner-index gap, uniformly over degree sections. -/
theorem integralGramFactor_eq_zero_of_separated_inner_gap
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)
    (hμ : Polynomial.HasFiniteMoments μ) (hpμ : Polynomial.HasPositiveDefiniteIntegral μ)
    (hν : Polynomial.HasFiniteMoments ν) (hpν : Polynomial.HasPositiveDefiniteIntegral ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hz : ∀ᵐ x ∂ν, x ∈ Icc (-1 : ℝ) 1)
    (h g : ℝ[X]) (l : ℕ) (hh0 : h ≠ 0) (hg0 : g ≠ 0)
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (hg : ∀ᵐ x ∂ν, 0 ≤ g.eval x)
    (hgpar : ∀ x, g.eval (-x) = g.eval x)
    (hgcoeff : ∀ i, i % 2 ≠ 0 → g.coeff i = 0) (hgdeg : g.natDegree ≤ 2 * l)
    (u : MvPolynomial (Fin 2) ℝ) (hu : ∀ᵐ x ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν), 0 ≤ eval x u)
    (hmod : u = cartesianDiskModification h g l)
    (hM : MvPolynomial.HasFiniteMoments
      (MvPolynomial.polynomialDensityMeasure (u) (((cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν))).comap Subtype.val)))
    (hP : MvPolynomial.HasPositiveDefiniteIntegral
      (MvPolynomial.polynomialDensityMeasure (u) (((cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν))).comap Subtype.val)))
    (N : ℕ) (i j : Fin (Fintype.card (DiskDegreeIndex N)))
    (hgap : (diskDegreeOrder N i).1 1 + g.natDegree < (diskDegreeOrder N j).1 1 ∨
      (diskDegreeOrder N j).1 1 + g.natDegree < (diskDegreeOrder N i).1 1) :
    integralGramFactor _ hM hP (S.orderedDegreeBasis hx hz N) i j = 0 := by
  let := (hμ.diskOuterModification hx h hh l).isFiniteMeasure
  let := (hν.polynomialDensityMeasure g hg).isFiniteMeasure
  have U := modifiedCartesianDiskSystem hμ hpμ hν hpν hx h g l hh0 hg0 hh hg hgpar
  have hzU : ∀ᵐ x ∂Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val),
      x ∈ Icc (-1 : ℝ) 1 := (polynomialDensityMeasure_comap_absolutelyContinuous g ν).ae_le hz
  rw [S.integralGramFactor_eq_orderedConnectionMatrix hx hz h g l U hμ hν hh hg
    hgpar hgdeg hzU _ hM hP (fun p q ↦ ?_) N, orderedConnectionMatrix_apply]
  · apply S.connectionEntry_eq_zero_of_inner_band h g l U hμ hν hx hh hg
    omega
  · rw [MvPolynomial.integralInner_withDensity_polynomial _ _ _ hu
      (hpq := (S.hasFiniteMoments hx).integrable_mul _ _)]
    simp only [hmod]
    exact (integralInner_cartesianDiskModification hμ hν hx hz h g l hh hg hgdeg hgcoeff p q).symm

end MvPolynomial.CartesianDiskSystem
