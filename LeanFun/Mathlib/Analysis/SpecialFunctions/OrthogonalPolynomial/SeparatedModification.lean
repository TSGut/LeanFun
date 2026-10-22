/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionGram
public import Mathlib.Algebra.Algebra.Operations

/-!
# Outer-variable modification of separated polynomial families

A fixed inner lift is unchanged by outer conversion. This algebraic statement
does not constrain its geometry or its total degree. Applying it separately at
each inner index is the Type 1 Koornwinder mechanism.
Reference: Dunkl–Xu, §2.6.1; Gutleb–Olver–Slevinsky, polynomial modification.
-/

public section
open MeasureTheory
namespace Polynomial.Sequence
variable {A : Type*} [CommRing A] [Algebra ℝ A]

/-- An outer polynomial expansion lifts through any algebra embedding and fixed
inner factor. In particular it introduces no other inner indices. -/
theorem IsOrthogonal.separated_expansion {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {Q : Sequence ℝ} (hQ : Q.IsOrthogonal μ)
    (hu : ∀ i, IsUnit (Q i).leadingCoeff)
    (φ : ℝ[X] →ₐ[ℝ] A) (v : A) (P : Sequence ℝ) (n : ℕ) :
    φ (P n) * v = ∑ m ∈ Finset.range (n+1),
      (Q.basis hu).repr (P n) m • (φ (Q m) * v) := by
  have he := congrArg (fun p => φ p * v)
    (hQ.sum_range_repr hμ hpos hu (P n) (n+1) (by simp))
  simpa only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc] using he.symm

/-- A polynomial outer modification admits an expansion using only the last
degree(u)+1 outer indices and the same fixed inner lift. -/
theorem IsOrthogonal.separated_modification_expansion {A : Type*} [CommRing A] [Algebra ℝ A]
    {u : ℝ[X]} {μ : Measure {x : ℝ // 0 ≤ u.eval x}}
    (hμ : HasFiniteMoments (μ.map Subtype.val))
    (hpos : HasPositiveDefiniteIntegral (μ.map Subtype.val)) (hu0 : u ≠ 0)
    {P Q : Sequence ℝ} (hP : P.IsOrthogonal (μ.map Subtype.val))
    (hQ : Q.IsOrthogonal (polynomialDensityMeasure u μ))
    (hunits : ∀ i, IsUnit (Q i).leadingCoeff)
    (φ : ℝ[X] →ₐ[ℝ] A) (v : A) (n : ℕ) :
    φ (P n) * v = ∑ m ∈ (Finset.range (n+1)).filter (fun m => n ≤ m+u.natDegree),
      (Q.basis hunits).repr (P n) m • (φ (Q m) * v) := by
  classical
  rw [hQ.separated_expansion (HasFiniteMoments.withDensity_polynomial hμ)
    (HasPositiveDefiniteIntegral.withDensity_polynomial hμ hpos hu0) hunits φ v P n]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro m hm hn
  have hout : m+u.natDegree < n := by
    simp only [Finset.mem_filter, hm, true_and, not_le] at hn
    exact hn
  rw [IsOrthogonal.basis_repr_eq_zero_of_polynomial_modification hμ hpos hu0 hP hQ hunits (Or.inr hout), zero_smul]

/-- Transport from a real source supported on the nonnegative locus. -/
theorem IsOrthogonal.separated_modification_expansion_comap {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (u : ℝ[X]) (hu0 : u ≠ 0) (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x)
    {P Q : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (hQ : Q.IsOrthogonal (Polynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)))
    (hunits : ∀ i, IsUnit (Q i).leadingCoeff)
    (φ : ℝ[X] →ₐ[ℝ] A) (v : A) (n : ℕ) :
    φ (P n) * v = ∑ m ∈ (Finset.range (n+1)).filter (fun m => n ≤ m+u.natDegree),
      (Q.basis hunits).repr (P n) m • (φ (Q m) * v)  := by
  have hm : HasFiniteMoments ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  have hp : HasPositiveDefiniteIntegral ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  have hP' : P.IsOrthogonal ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  exact IsOrthogonal.separated_modification_expansion hm hp hu0 hP' hQ hunits φ v n

end Polynomial.Sequence
