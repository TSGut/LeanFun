/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Pairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Normalization
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Parity

/-!
# Orthonormal Cartesian disk systems

Positive-leading one-dimensional orthonormal sequences give the general
Cartesian construction, with an outer sequence for each inner degree.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

@[expose] public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- One-dimensional data for a normalized Cartesian disk system. -/
structure CartesianDiskSystem (μ : Measure (Icc (-1 : ℝ) 1)) (ν : Measure ℝ) where
  /-- The degree-dependent outer sequences. -/
  outer : ℕ → Polynomial.Sequence ℝ
  /-- The common inner sequence. -/
  inner : Polynomial.Sequence ℝ
  /-- The inner measure is an orthogonality measure. -/
  inner_orthogonal : inner.IsOrthogonal ν
  /-- The outer measure carries the inner-degree density shift. -/
  outer_orthogonal : ∀ k, (outer k).IsOrthogonal (diskOuterMeasure k ((μ.map Subtype.val).comap Subtype.val))
  /-- Parity makes each lifted inner factor polynomial. -/
  inner_parity : ∀ k i, i % 2 ≠ k % 2 → (inner k).coeff i = 0
  /-- Positive inner leading coefficients fix orientation. -/
  inner_leadingCoeff_pos : ∀ k, 0 < (inner k).leadingCoeff
  /-- Positive outer leading coefficients fix orientation. -/
  outer_leadingCoeff_pos : ∀ k n, 0 < (outer k n).leadingCoeff
  /-- Inner sequences have unit squared norm. -/
  inner_norm : ∀ k, ∫ x, (inner k).eval x ^ 2 ∂ν = 1
  /-- Outer sequences have unit squared norm. -/
  outer_norm : ∀ k n, ∫ x, (outer k n).eval x ^ 2 ∂diskOuterMeasure k ((μ.map Subtype.val).comap Subtype.val) = 1

/-- Internal supported-real transport of outer orthogonality. -/
theorem CartesianDiskSystem.outer_orthogonal_real {μ ν : Measure ℝ}
    (S : CartesianDiskSystem (μ.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)) ν) (k : ℕ)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    (S.outer k).IsOrthogonal (diskOuterMeasure k (μ.comap Subtype.val)) := by
  simpa only [map_comap_subtype_coe measurableSet_Icc,
    Measure.restrict_eq_self_of_ae_mem hx] using S.outer_orthogonal k

/-- Internal supported-real transport of outer normalization. -/
theorem CartesianDiskSystem.outer_norm_real {μ ν : Measure ℝ}
    (S : CartesianDiskSystem (μ.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)) ν) (k n : ℕ)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    ∫ x, (S.outer k n).eval x ^ 2 ∂diskOuterMeasure k (μ.comap Subtype.val) = 1 := by
  simpa only [map_comap_subtype_coe measurableSet_Icc,
    Measure.restrict_eq_self_of_ae_mem hx] using S.outer_norm k n

/-- The inner family supplies all inner moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem CartesianDiskSystem.hasFiniteMoments_inner {μ : Measure (Icc (-1 : ℝ) 1)} {ν : Measure ℝ}
    (S : CartesianDiskSystem μ ν) : Polynomial.HasFiniteMoments ν :=
  S.inner_orthogonal.hasFiniteMoments

/-- The zero-degree outer family supplies every coordinate moment on the typed source. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem CartesianDiskSystem.hasFiniteMoments_outer {μ : Measure (Icc (-1 : ℝ) 1)} {ν : Measure ℝ}
    (S : CartesianDiskSystem μ ν) : Polynomial.HasFiniteMoments (μ.map Subtype.val) := by
  simpa only [diskOuterMeasure_zero] using (S.outer_orthogonal 0).hasFiniteMoments

/-- Internal supported-real transport of outer moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem CartesianDiskSystem.hasFiniteMoments_outer_real {μ ν : Measure ℝ}
    (S : CartesianDiskSystem (μ.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)) ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) : Polynomial.HasFiniteMoments μ := by
  simpa only [map_comap_subtype_coe measurableSet_Icc,
    Measure.restrict_eq_self_of_ae_mem hx] using S.hasFiniteMoments_outer

/-- All Cartesian polynomial pairs are integrable under the standard outer support. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem CartesianDiskSystem.hasFiniteMoments {μ ν : Measure ℝ}
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) :
    MvPolynomial.HasFiniteMoments (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (hν := by let := S.hasFiniteMoments_inner.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) :=
  hasFiniteMoments_cartesianDiskMeasure_of_moments (S.hasFiniteMoments_outer_real hx) S.hasFiniteMoments_inner hx

/-- Such systems exist for nondegenerate factors with even inner measure. -/
noncomputable def cartesianDiskSystem (μ ν : Measure ℝ) [ν.IsNegInvariant]
    (hμ : Polynomial.HasFiniteMoments μ) (hμpos : Polynomial.HasPositiveDefiniteIntegral μ)
    (hν : Polynomial.HasFiniteMoments ν) (hνpos : Polynomial.HasPositiveDefiniteIntegral ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν := by
  classical
  choose Q hQ hQl hQn using exists_positive_orthonormal_sequence ν hν hνpos
  have he (k : ℕ) := exists_positive_orthonormal_sequence (diskOuterMeasure k (μ.comap Subtype.val))
    (hμ.diskOuterMeasure hx k) (hμpos.diskOuterMeasure hμ hx k)
  choose P hP hPl hPn using he
  refine ⟨P,Q,hQ,?_,hQ.coeff_eq_zero_of_parity hν hνpos,hQl,hPl,hQn,?_⟩
  · simpa only [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem hx] using hP
  · simpa only [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem hx] using hPn

namespace CartesianDiskSystem
section
variable {μ : Measure (Icc (-1 : ℝ) 1)} {ν : Measure ℝ} (S : CartesianDiskSystem μ ν)

/-- The Cartesian polynomial at total degree n and inner degree k. -/
noncomputable def polynomial (n k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  cartesianDiskPolynomial (S.outer k (n-k)) (S.inner k) k

/-- Total degree is at most the first index. -/
theorem totalDegree_polynomial_le {n k : ℕ} (hk : k ≤ n) :
    (S.polynomial n k).totalDegree ≤ n := by
  exact (totalDegree_cartesianDiskPolynomial_le _ _ _).trans
    (by simp only [Sequence.natDegree_eq]; omega)

end

variable {μ ν : Measure ℝ} (S : CartesianDiskSystem (μ.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)) ν)

/-- Distinct valid Cartesian indices are orthogonal. -/
theorem integralInner_polynomial_eq_zero [SFinite μ] [SFinite ν]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m) (hne : (n,k) ≠ (m,j)) :
    integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (hν := by let := S.hasFiniteMoments_inner.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (hν := by let := S.hasFiniteMoments_inner.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (S.polynomial n k) (S.polynomial m j)) = 0 := by
  have hm : Measure.map (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
      (μ.comap Subtype.val) = μ := by
    rw [map_comap_subtype_coe measurableSet_Icc, Measure.restrict_eq_self_of_ae_mem hx]
  by_cases hkj : k=j
  · subst j
    dsimp only [polynomial]
    rw [integralInner_cartesianDiskPolynomial_same_degree hx
      _ _ _ _ k (by simp) (by simp) (S.inner_parity k) (S.inner_parity k)]
    rw [show Polynomial.integralInner (diskOuterMeasure k (μ.comap Subtype.val)) (Polynomial.IntegrablePair.of (diskOuterMeasure k (μ.comap Subtype.val)) (S.outer k (n-k)) (S.outer k (m-k))) = 0 from
      (S.outer_orthogonal_real k).orthogonal _ _ (by intro h; apply hne; congr 1; omega), zero_mul]
  · dsimp only [polynomial]
    rw [integralInner_cartesianDiskPolynomial hx
      _ _ _ _ k j (by simp) (by simp) (S.inner_parity k) (S.inner_parity j)]
    rw [show Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (S.inner k) (S.inner j)) = 0 from
      S.inner_orthogonal.orthogonal k j hkj, mul_zero]

/-- Every Cartesian polynomial has unit squared norm. -/
theorem integralInner_polynomial_self [SFinite μ] [SFinite ν]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (n k : ℕ) :
    integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (hν := by let := S.hasFiniteMoments_inner.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (hν := by let := S.hasFiniteMoments_inner.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (S.polynomial n k) (S.polynomial n k)) = 1 := by
  dsimp only [polynomial]
  rw [integralInner_cartesianDiskPolynomial_same_degree hx
    _ _ _ _ k (by simp) (by simp) (S.inner_parity k) (S.inner_parity k)]
  simp only [Polynomial.integralInner_self, S.outer_norm_real, S.inner_norm, one_mul]

end CartesianDiskSystem
end MvPolynomial
