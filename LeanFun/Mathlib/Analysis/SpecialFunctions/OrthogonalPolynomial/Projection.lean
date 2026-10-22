/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Approximation

/-!
# Polynomial representatives of finite weighted projections

The degree-N partial sum has a canonical polynomial representative. It fixes
polynomials of degree at most N and is a contraction in weighted L².
Reference: DLMF 18.2(viii); ATAP, Chapter 16.
-/

public section
open Real MeasureTheory
open scoped InnerProductSpace
namespace Polynomial
variable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)

/-- Positive definiteness makes polynomial evaluation into L² injective. -/
theorem polynomialToL2_injective (hpos : HasPositiveDefiniteIntegral μ) :
    Function.Injective (polynomialToL2 hμ) := by
  have hz (p : ℝ[X]) (hp : polynomialToL2 hμ p = 0) : p = 0 := by
    by_contra hn
    have h := hpos p hn
    have he := inner_polynomialToL2 hμ p p
    rw [hp, inner_zero_left] at he
    have he' : (∫ x, p.eval x ^ 2 ∂μ) = 0 := by
      simpa only [pow_two] using he.symm
    rw [he'] at h
    exact (lt_irrefl 0) h
  intro p q he
  exact sub_eq_zero.mp (hz (p - q) (by rw [map_sub, he, sub_self]))

namespace Sequence
variable (P : Sequence ℝ)

/-- The degree-N integral-coefficient partial sum, in the original normalization. -/
@[expose] noncomputable def partialSum (μ : Measure ℝ) {N : ℕ}
    (f : IntegralCoefficientFamilyInput ℝ μ P N) : ℝ[X] :=
  ∑ i : Fin (N + 1), P.integralCoefficient μ (f.at i) • P i

/-- The finite polynomial formula on the classical input domain. -/
theorem partialSum_apply (μ : Measure ℝ) {N : ℕ}
    (f : IntegralCoefficientFamilyInput ℝ μ P N) :
    P.partialSum μ f = ∑ i : Fin (N + 1), P.integralCoefficient μ (f.at i) • P i := rfl

/-- The partial-sum polynomial has degree at most its truncation index. -/
theorem degree_partialSum_le {N : ℕ} (f : IntegralCoefficientFamilyInput ℝ μ P N) :
    (P.partialSum μ f).degree ≤ N := by
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro i hi
  exact (degree_smul_le _ _).trans (by simpa only [P.degree_eq, Nat.cast_le] using
    (Nat.lt_succ_iff.mp i.isLt))

/-- Internal range-indexed formula for L2 data. -/
theorem partialSum_ofL2 (hpos : HasPositiveDefiniteIntegral μ)
    (f : Lp ℝ 2 μ) (N : ℕ) :
    P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N) =
      ∑ i ∈ Finset.range (N + 1), P.integralCoefficient μ
        (IntegralCoefficientInput.ofL2 hμ hpos (P i) (P.ne_zero i) f) • P i := by
  simp only [partialSum, IntegralCoefficientFamilyInput.ofL2_at]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ P.integralCoefficient μ
    (IntegralCoefficientInput.ofL2 hμ hpos (P i) (P.ne_zero i) f) • P i) (N + 1)


variable {P}

/-- Polynomial partial sums represent finite orthonormal projections in L². -/
theorem polynomialToL2_partialSum (hpos : HasPositiveDefiniteIntegral μ)
    (f : Lp ℝ 2 μ) (N : ℕ) :
    polynomialToL2 hμ (P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N)) =
      ∑ i ∈ Finset.range (N + 1), inner ℝ (P.normalizedToL2 hμ ⟨i, squaredNorm_pos hpos P i⟩) f •
        P.normalizedToL2 hμ ⟨i, squaredNorm_pos hpos P i⟩ := by
  simp only [partialSum_ofL2, map_sum, map_smul, inner_normalizedToL2_smul hμ hpos]

/-- Projection reproduces every polynomial of degree at most N. -/
theorem IsOrthogonal.partialSum_polynomialToL2 (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (N : ℕ) (p : ℝ[X]) (hp : p.degree ≤ N) :
    P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P (polynomialToL2 hμ p) N) = p := by
  apply polynomialToL2_injective hμ hpos
  rw [polynomialToL2_partialSum hμ hpos]
  exact (hP.orthonormal_normalizedToL2 hμ hpos).sum_inner_smul_eq_of_mem_span _ _
    (polynomialToL2_mem_span_normalizedToL2 hμ hpos N p hp)

include hμ in
/-- Subtracting data subtracts their projection polynomials. -/
theorem partialSum_sub (hpos : HasPositiveDefiniteIntegral μ)
    (f g : Lp ℝ 2 μ) (N : ℕ) :
    P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P (f - g : Lp ℝ 2 μ) N) = P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N) - P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P g N) := by
  apply polynomialToL2_injective hμ hpos
  simp only [map_sub, polynomialToL2_partialSum hμ hpos, inner_sub_right,
    sub_smul, Finset.sum_sub_distrib]

/-- Weighted polynomial projection is a contraction in L². -/
theorem IsOrthogonal.norm_polynomialToL2_partialSum_le (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (f : Lp ℝ 2 μ) (N : ℕ) :
    ‖polynomialToL2 hμ (P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N))‖ ≤ ‖f‖ := by
  rw [polynomialToL2_partialSum hμ hpos]
  exact (hP.orthonormal_normalizedToL2 hμ hpos).norm_sum_inner_smul_le _ _

end Sequence
end Polynomial
