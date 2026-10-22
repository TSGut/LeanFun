/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.System
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Modification

/-!
# Existence of the modified Cartesian system

Nonzero nonnegative polynomial factors preserve nondegeneracy. Thus the target
systems used in the support theorem exist, including when the modifying density
vanishes on interior lines.
Reference: Gautschi, polynomial measure modification; Dunkl–Xu, Chapter 3.
-/

@[expose] public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- Construct the target orthonormal system for a separated polynomial modification. -/
noncomputable def modifiedCartesianDiskSystem {μ ν : Measure ℝ} [ν.IsNegInvariant]
    (hμ : Polynomial.HasFiniteMoments μ) (hμpos : Polynomial.HasPositiveDefiniteIntegral μ)
    (hν : Polynomial.HasFiniteMoments ν) (hνpos : Polynomial.HasPositiveDefiniteIntegral ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (h g : ℝ[X]) (l : ℕ) (hh0 : h ≠ 0) (hg0 : g ≠ 0)
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (hg : ∀ᵐ z ∂ν, 0 ≤ g.eval z)
    (hgpar : ∀ x, g.eval (-x) = g.eval x) :
    CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure g (ν.comap Subtype.val)) := by
  let := isNegInvariant_polynomialDensityMeasure_comap g ν hgpar
  exact cartesianDiskSystem _ _ (hμ.diskOuterModification hx h hh l)
    (hμpos.diskOuterModification hμ hx h hh0 hh l)
    (hν.polynomialDensityMeasure g hg) (hνpos.polynomialDensityMeasure hν g hg0 hg)
    (ae_mem_diskOuterModification hx h l)

end MvPolynomial
