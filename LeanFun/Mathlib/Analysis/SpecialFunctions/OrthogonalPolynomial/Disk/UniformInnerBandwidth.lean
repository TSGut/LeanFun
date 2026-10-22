/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.OrderedBasis
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.PolynomialDensityMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.GramFactor

/-! # Uniform inner bandwidth over Cartesian factor measures
The bound precedes both the factor measures and the finite degree section.
The ordering is total degree then inner degree. Reference: the uniform
Cartesian measure-modification sparsity question.
-/

@[expose] public section
open MeasureTheory Set Polynomial Module
namespace MvPolynomial

/-- One inner bandwidth for canonical factors over all admissible Cartesian
factor measures and all complete degree sections. The inner measure is even;
no outer reflection hypothesis is required. -/
def HasUniformCartesianInnerBandwidth (u : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∃ w : ℕ, ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ν.IsNegInvariant],
    Polynomial.HasFiniteMoments μ → Polynomial.HasPositiveDefiniteIntegral μ →
    Polynomial.HasFiniteMoments ν → Polynomial.HasPositiveDefiniteIntegral ν →
    ∀ (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hz : ∀ᵐ x ∂ν, x ∈ Icc (-1 : ℝ) 1)
      (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (N : ℕ),
    ∀ (_hu : ∀ᵐ x ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν), 0 ≤ eval x u),
    let ω := polynomialDensityMeasure u ((cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)).comap Subtype.val)
    ∀ (hM : MvPolynomial.HasFiniteMoments ω) (hP : MvPolynomial.HasPositiveDefiniteIntegral ω)
      (i j : Fin (Fintype.card (DiskDegreeIndex N))),
      (diskDegreeOrder N i).1 1 + w < (diskDegreeOrder N j).1 1 ∨
        (diskDegreeOrder N j).1 1 + w < (diskDegreeOrder N i).1 1 →
      integralGramFactor ω hM hP (S.orderedDegreeBasis hx hz N) i j = 0

end MvPolynomial
