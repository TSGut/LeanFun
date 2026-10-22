/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionSupport
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Operators
public import LeanFun.Mathlib.LinearAlgebra.Basis.BandedCoefficientMap

/-!
# Polynomial measure conversion as a banded operator

Conversions act on finitely supported coefficients. Successive conversions
compose exactly and intertwine multiplication; no finite-section similarity
or multiplication of arbitrary infinite matrices is asserted.
Reference: Gutleb–Olver–Slevinsky, polynomial measure modifications, Lemma 2.8.
-/

public section
open MeasureTheory Module
namespace Polynomial.Sequence

/-- Multiplication by any polynomial of degree d has lower and upper bandwidth d
in an orthogonal basis, independently of the support of the measure. -/
theorem IsOrthogonal.polynomial_mul_isBanded {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (hu : ∀ i, IsUnit (P i).leadingCoeff) (u : ℝ[X]) :
    ((P.basis hu).toMatrix (fun j => u * P j)).IsBanded u.natDegree u.natDegree := by
  intro i j hij
  rw [Basis.toMatrix_apply, hP.basis_repr_eq_integralInner_div hμ hpos hu]
  suffices hz : integralInner μ (IntegrablePair.of μ (u * P j) (P i)) = 0 by rw [hz, zero_div]
  have hs : integralInner μ (IntegrablePair.of μ (u * P j) (P i)) = integralInner μ (IntegrablePair.of μ (u * P i) (P j)) := by
    unfold integralInner
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [eval_mul]
    ring
  rcases hij with h | h
  · apply hP.integralInner_eq_zero_of_degree_lt hμ
    have hd : (u * P j).natDegree < i := natDegree_mul_le.trans_lt (by
      simpa only [P.natDegree_eq, Nat.add_comm] using h)
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hd)
  · rw [hs]
    apply hP.integralInner_eq_zero_of_degree_lt hμ
    have hd : (u * P i).natDegree < j := natDegree_mul_le.trans_lt (by
      simpa only [P.natDegree_eq, Nat.add_comm] using h)
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hd)

/-- A degree-d nonnegative polynomial measure modification has upper bandwidth d. -/
theorem IsOrthogonal.conversion_isBanded {u : ℝ[X]} {μ : Measure {x : ℝ // 0 ≤ u.eval x}}
    (hμ : HasFiniteMoments (μ.map Subtype.val))
    (hpos : HasPositiveDefiniteIntegral (μ.map Subtype.val)) (hu0 : u ≠ 0)
    {P Q : Sequence ℝ} (hP : P.IsOrthogonal (μ.map Subtype.val))
    (hQ : Q.IsOrthogonal (polynomialDensityMeasure u μ))
    (hunits : ∀ i, IsUnit (Q i).leadingCoeff) :
    ((Q.basis hunits).toMatrix P).IsBanded 0 u.natDegree := by
  intro i j hij
  exact IsOrthogonal.basis_repr_eq_zero_of_polynomial_modification hμ hpos hu0 hP hQ hunits (by simpa using hij)


/-- Transport from a real source supported on the nonnegative locus. -/
theorem IsOrthogonal.conversion_isBanded_comap {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (u : ℝ[X]) (hu0 : u ≠ 0) (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x)
    {P Q : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (hQ : Q.IsOrthogonal (Polynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)))
    (hunits : ∀ i, IsUnit (Q i).leadingCoeff) :
    ((Q.basis hunits).toMatrix P).IsBanded 0 u.natDegree  := by
  have hm : HasFiniteMoments ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  have hp : HasPositiveDefiniteIntegral ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  have hP' : P.IsOrthogonal ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  exact IsOrthogonal.conversion_isBanded hm hp hu0 hP' hQ hunits

/-- Two upper-banded changes of polynomial basis have the sum of the bandwidths.
This applies to compatible successive measure modifications without requiring
the intermediate family to be classical. -/
theorem conversion_isBanded_trans (P Q S : Sequence ℝ)
    (hP : ∀ i, IsUnit (P i).leadingCoeff)
    (hQ : ∀ i, IsUnit (Q i).leadingCoeff)
    (hS : ∀ i, IsUnit (S i).leadingCoeff) {d e : ℕ}
    (hPQ : ((Q.basis hQ).toMatrix P).IsBanded 0 d)
    (hQS : ((S.basis hS).toMatrix Q).IsBanded 0 e) :
    ((S.basis hS).toMatrix P).IsBanded 0 (d+e) := by
  simpa only [basis_eq_self, LinearMap.id_apply, Nat.zero_add] using
    (P.basis hP).toMatrix_comp_isBanded (Q.basis hQ) (S.basis hS)
      LinearMap.id LinearMap.id
      (by simpa only [basis_eq_self, LinearMap.id_apply] using hPQ)
      (by simpa only [basis_eq_self, LinearMap.id_apply] using hQS)

/-- Multiplication by x in the two bases is intertwined by conversion.
The identity acts on finite expansions of every degree. -/
theorem conversion_intertwines_multiplication (P Q : Sequence ℝ)
    (hP : ∀ i, IsUnit (P i).leadingCoeff)
    (hQ : ∀ i, IsUnit (Q i).leadingCoeff) :
    ((P.basis hP).coefficientMap (Q.basis hQ) LinearMap.id).comp
        ((P.basis hP).coefficientMap (P.basis hP) (LinearMap.mulLeft ℝ X)) =
      ((Q.basis hQ).coefficientMap (Q.basis hQ) (LinearMap.mulLeft ℝ X)).comp
        ((P.basis hP).coefficientMap (Q.basis hQ) LinearMap.id) :=
  (P.basis hP).coefficientMap_id_intertwines (Q.basis hQ) (LinearMap.mulLeft ℝ X)

end Polynomial.Sequence
