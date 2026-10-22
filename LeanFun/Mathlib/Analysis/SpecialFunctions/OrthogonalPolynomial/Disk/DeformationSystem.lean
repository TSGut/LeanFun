/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.DeformationPairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.System
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.DeformationCoordinates
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Identification of deformed Cartesian systems

Positive-leading orthonormal normalization fixes both factors uniquely.
The even-even sector is identified with the source system under deformation.
Reference: Dunkl–Xu, §2.6.1; Szegő, Chapter 3.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial.CartesianDiskSystem

/-- Even outer polynomials in the two systems agree after normalized transport. -/
theorem outer_even_diskDeformation_eq
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [μ.IsNegInvariant]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hμ : Polynomial.HasFiniteMoments μ) (hμpos : Polynomial.HasPositiveDefiniteIntegral μ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδpos : Polynomial.HasPositiveDefiniteIntegral (diskDeformedMeasure δ (μ.comap Subtype.val)))
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ (μ.comap Subtype.val))) ν)
    (a b : ℕ) :
    δ⁻¹^b • evenDiskTransport ⟨δ,hδ.ne'⟩ (S.outer (2*b) (2*a)) = T.outer (2*b) (2*a) := by
  let := isNegInvariant_diskOuterMeasure μ (2*b)
  let := isNegInvariant_diskOuterMeasure (diskDeformedMeasure δ (μ.comap Subtype.val)) (2*b)
  have hδmom := hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx
  have hδsupp := ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx
  apply normalized_evenDiskTransport_eq hx hμ hδ hδ1 b (2*a)
    (hδpos.diskOuterMeasure hδmom hδsupp (2*b))
    (S.outer_orthogonal_real (2*b)) (T.outer_orthogonal_real (2*b))
  · intro i hi
    exact (S.outer_orthogonal_real (2*b)).coeff_eq_zero_of_parity
      (hμ.diskOuterMeasure hx (2*b)) (hμpos.diskOuterMeasure hμ hx (2*b))
      (2*a) i (by simpa using hi)
  · intro i hi
    exact (T.outer_orthogonal_real (2*b)).coeff_eq_zero_of_parity
      (hδmom.diskOuterMeasure hδsupp (2*b)) (hδpos.diskOuterMeasure hδmom hδsupp (2*b))
      (2*a) i (by simpa using hi)
  · exact S.outer_leadingCoeff_pos _ _
  · exact T.outer_leadingCoeff_pos _ _
  · simpa only [Polynomial.integralInner_self] using S.outer_norm_real (2*b) (2*a)
  · simpa only [Polynomial.integralInner_self] using T.outer_norm_real (2*b) (2*a)

/-- The normalized inner factors depend only on their common measure. -/
theorem inner_eq {μ μ' ν : Measure ℝ}
    (hν : Polynomial.HasFiniteMoments ν) (hνpos : Polynomial.HasPositiveDefiniteIntegral ν)
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') ν) (n : ℕ) :
    S.inner n = T.inner n := by
  let c := (S.inner n).leadingCoeff / (T.inner n).leadingCoeff
  have hc : 0 < c := div_pos (S.inner_leadingCoeff_pos n) (T.inner_leadingCoeff_pos n)
  have he : S.inner n = c • T.inner n :=
    T.inner_orthogonal.eq_leadingCoeff_div_smul hν hνpos S.inner_orthogonal n
  have hn := S.inner_norm n
  rw [he] at hn
  simp only [Polynomial.eval_smul, smul_eq_mul, mul_pow, integral_const_mul, T.inner_norm] at hn
  have hc1 : c = 1 := by nlinarith
  simpa [hc1] using he
/-- Canonical even-even disk polynomials agree on corresponding deformed slices. -/
theorem eval_polynomial_diskDeformation
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [μ.IsNegInvariant]
    (hxμ : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hμ : Polynomial.HasFiniteMoments μ) (hμpos : Polynomial.HasPositiveDefiniteIntegral μ)
    (hν : Polynomial.HasFiniteMoments ν) (hνpos : Polynomial.HasPositiveDefiniteIntegral ν)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδpos : Polynomial.HasPositiveDefiniteIntegral (diskDeformedMeasure δ (μ.comap Subtype.val)))
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ (μ.comap Subtype.val))) ν)
    (a b : ℕ) (x t z : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hxt : x^2 = 1-δ+δ*t^2) :
    eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (x,z)) (T.polynomial (2*a+2*b) (2*b)) =
      eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (t,z)) (S.polynomial (2*a+2*b) (2*b)) := by
  simp only [polynomial, Nat.add_sub_cancel]
  rw [← S.outer_even_diskDeformation_eq hxμ hμ hμpos hδ hδ1 hδpos T a b,
    ← S.inner_eq hν hνpos T (2*b)]
  apply eval_cartesianDiskPolynomial_evenDiskTransport hδ b _ _ _ (by simp)
    (S.inner_parity (2*b)) x t z hx ht hxt
  intro i hi
  let := isNegInvariant_diskOuterMeasure μ (2*b)
  exact (S.outer_orthogonal_real (2*b)).coeff_eq_zero_of_parity
    (hμ.diskOuterMeasure hxμ (2*b)) (hμpos.diskOuterMeasure hμ hxμ (2*b))
    (2*a) i (by simpa using hi)

/-- The modified Gram entries of the canonical even-even sector form an affine pencil. -/
theorem integral_quadratic_polynomial_diskDeformation
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.IsNegInvariant]
    (hxμ : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hzν : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)
    (hμ : Polynomial.HasFiniteMoments μ) (hμpos : Polynomial.HasPositiveDefiniteIntegral μ)
    (hν : Polynomial.HasFiniteMoments ν) (hνpos : Polynomial.HasPositiveDefiniteIntegral ν)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδpos : Polynomial.HasPositiveDefiniteIntegral (diskDeformedMeasure δ (μ.comap Subtype.val)))
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ (μ.comap Subtype.val))) ν)
    (a b c d : ℕ) (A B C : ℝ) :
    (∫ v, (A+B*(v 0)^2+C*(v 1)^2)*
      (eval v (T.polynomial (2*a+2*b) (2*b))*eval v (T.polynomial (2*c+2*d) (2*d)))
      ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ (μ.comap Subtype.val))) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ (μ.comap Subtype.val))) ν)) =
    ∫ v, ((A+B)+δ*(C*(v 1)^2-B*(1-(v 0)^2)))*
      (eval v (S.polynomial (2*a+2*b) (2*b))*eval v (S.polynomial (2*c+2*d) (2*d)))
      ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) := by
  apply integral_quadratic_diskDeformedMeasure hxμ hzν hδ.le hδ1 A B C
    ((T.polynomial (2*a+2*b) (2*b)).continuous_eval.mul
      (T.polynomial (2*c+2*d) (2*d)).continuous_eval)
    ((S.polynomial (2*a+2*b) (2*b)).continuous_eval.mul
      (S.polynomial (2*c+2*d) (2*d)).continuous_eval)
  · intro t ht z _
    exact congrArg₂ (fun u v : ℝ => u*v)
      (S.eval_polynomial_diskDeformation hxμ hμ hμpos hν hνpos hδ hδ1 hδpos T
        a b _ t z (diskDeformation_mem_Icc_of_unitInterval hδ.le hδ1 ht) ht (diskDeformation_sq_of_unitInterval hδ.le hδ1 t))
      (S.eval_polynomial_diskDeformation hxμ hμ hμpos hν hνpos hδ hδ1 hδpos T
        c d _ t z (diskDeformation_mem_Icc_of_unitInterval hδ.le hδ1 ht) ht (diskDeformation_sq_of_unitInterval hδ.le hδ1 t))
  · intro t ht z _
    have hn : -diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ.le hδ1 t⟩ ∈ Icc (-1 : ℝ) 1 := by
      have hh := diskDeformation_mem_Icc_of_unitInterval hδ.le hδ1 ht
      constructor <;> linarith [hh.1,hh.2]
    have hs : (-diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ.le hδ1 t⟩)^2 = 1-δ+δ*t^2 := by
      simpa using diskDeformation_sq_of_unitInterval hδ.le hδ1 t
    exact congrArg₂ (fun u v : ℝ => u*v)
      (S.eval_polynomial_diskDeformation hxμ hμ hμpos hν hνpos hδ hδ1 hδpos T
        a b _ t z hn ht hs)
      (S.eval_polynomial_diskDeformation hxμ hμ hμpos hν hνpos hδ hδ1 hδpos T
        c d _ t z hn ht hs)

end MvPolynomial.CartesianDiskSystem
