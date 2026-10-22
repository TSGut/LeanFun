/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.HilbertBasis
public import LeanFun.Mathlib.Analysis.InnerProductSpace.FiniteProjection

/-!
# Best approximation by weighted orthogonal polynomial projections

Finite projections require finite moments and positive definiteness, but no
completeness or support geometry. A uniform competitor bound gives a weighted
L² error bound with the square root of the total mass.
References: DLMF 18.2(viii); ATAP, Chapter 16.
-/

public section
open Real MeasureTheory
open scoped InnerProductSpace ENNReal
namespace Polynomial
variable {μ : Measure ℝ}

/-- A uniform almost-everywhere error gives the usual finite-measure L² bound. -/
theorem norm_sub_polynomialToL2_le_of_ae_bound (hμ : HasFiniteMoments μ)
    (f : Lp ℝ 2 μ) (p : ℝ[X]) {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ᵐ x ∂μ, ‖f x - p.eval x‖ ≤ ε) :
    ‖f - polynomialToL2 hμ p‖ ≤ √(μ.real Set.univ) * ε := by
  let := hμ.isFiniteMeasure
  have hb : ‖f - polynomialToL2 hμ p‖ ≤
      (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * ε := by
    apply Lp.norm_le_of_ae_bound hε
    filter_upwards [he, coe_polynomialToL2 hμ p,
      Lp.coeFn_sub f (polynomialToL2 hμ p)] with x hx hpx hsub
    simpa only [hsub, Pi.sub_apply, hpx] using hx
  norm_num only [ENNReal.toReal_ofNat] at hb
  simpa only [Real.sqrt_eq_rpow, one_div, measureUnivNNReal, Measure.real, ENNReal.toReal] using hb

end Polynomial

namespace Polynomial.Sequence
variable {μ : Measure ℝ} {P : Sequence ℝ} (hμ : HasFiniteMoments μ)

/-- A normalized inner-product term is the usual integral-coefficient term. -/
theorem inner_normalizedToL2_smul (hpos : HasPositiveDefiniteIntegral μ)
    (f : Lp ℝ 2 μ) (n : ℕ) :
    inner ℝ (P.normalizedToL2 hμ ⟨n, squaredNorm_pos hpos P n⟩) f • P.normalizedToL2 hμ ⟨n, squaredNorm_pos hpos P n⟩ =
      P.integralCoefficient μ (IntegralCoefficientInput.ofL2 hμ hpos (P n) (P.ne_zero n) f) • polynomialToL2 hμ (P n) := by
  rw [normalizedToL2, inner_smul_left, inner_polynomialToL2_left]
  simp only [conj_trivial, smul_smul]
  congr 1
  calc
    _ = ((√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ * (√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹) *
        (∫ x, f x * (P n).eval x ∂μ) := by ring
    _ = _ := by
      rw [← mul_inv, Real.mul_self_sqrt (squaredNorm_pos hpos P n).le]
      rfl

/-- Every polynomial of degree at most N belongs to the first N+1 normalized
polynomial classes. No density or compact-support hypothesis is needed. -/
theorem polynomialToL2_mem_span_normalizedToL2 (hpos : HasPositiveDefiniteIntegral μ)
    (N : ℕ) (p : ℝ[X]) (hp : p.degree ≤ N) :
    polynomialToL2 hμ p ∈ Submodule.span ℝ
      ((fun n ↦ P.normalizedToL2 hμ ⟨n, squaredNorm_pos hpos P n⟩) '' (Finset.range (N + 1) : Set ℕ)) := by
  have hs : p ∈ Submodule.span ℝ (P '' Set.Iic N) := by
    rw [P.span_degreeLE (fun i _ ↦ isUnit_iff_ne_zero.mpr
      (leadingCoeff_ne_zero.mpr (P.ne_zero i)))]
    exact mem_degreeLE.mpr hp
  clear hp
  induction hs using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨i, hi, rfl⟩ := hq
    have hz : √(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)) ≠ 0 :=
      (Real.sqrt_pos.mpr (squaredNorm_pos hpos P i)).ne'
    have hm := (Submodule.span ℝ
      ((fun n ↦ P.normalizedToL2 hμ ⟨n, squaredNorm_pos hpos P n⟩) '' (Finset.range (N + 1) : Set ℕ))).smul_mem
      (√(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _))) (Submodule.subset_span
        (Set.mem_image_of_mem _ (show i ∈ (Finset.range (N + 1) : Set ℕ) by
          simpa only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff, Set.mem_Iic] using hi)))
    simpa only [normalizedToL2, smul_smul, mul_inv_cancel₀ hz, one_smul] using hm
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using Submodule.add_mem _ hp hq
  | smul c p _ hp => simpa only [map_smul] using Submodule.smul_mem _ c hp

/-- The weighted degree-N orthogonal projection is at least as accurate in L²
as every polynomial competitor of degree at most N. -/
theorem IsOrthogonal.norm_sub_sum_integralCoefficient_le (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (f : Lp ℝ 2 μ) (N : ℕ)
    (p : ℝ[X]) (hp : p.degree ≤ N) :
    ‖f - ∑ i ∈ Finset.range (N + 1),
      P.integralCoefficient μ (IntegralCoefficientInput.ofL2 hμ hpos (P i) (P.ne_zero i) f) • polynomialToL2 hμ (P i)‖ ≤
      ‖f - polynomialToL2 hμ p‖ := by
  simpa only [inner_normalizedToL2_smul hμ hpos] using
    (hP.orthonormal_normalizedToL2 hμ hpos).norm_sub_sum_inner_le_of_mem_span
      (Finset.range (N + 1)) f (polynomialToL2 hμ p)
      (polynomialToL2_mem_span_normalizedToL2 hμ hpos N p hp)

/-- An almost-everywhere uniform competitor error bounds the weighted projection
error by the square root of the total mass times that error. -/
theorem IsOrthogonal.norm_sub_sum_integralCoefficient_le_of_ae_bound
    (hP : P.IsOrthogonal μ) (hpos : HasPositiveDefiniteIntegral μ)
    (f : Lp ℝ 2 μ) (N : ℕ) (p : ℝ[X]) (hp : p.degree ≤ N)
    {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ᵐ x ∂μ, ‖f x - p.eval x‖ ≤ ε) :
    ‖f - ∑ i ∈ Finset.range (N + 1),
      P.integralCoefficient μ (IntegralCoefficientInput.ofL2 hμ hpos (P i) (P.ne_zero i) f) • polynomialToL2 hμ (P i)‖ ≤
      √(μ.real Set.univ) * ε := by
  exact (hP.norm_sub_sum_integralCoefficient_le hμ hpos f N p hp).trans
    (norm_sub_polynomialToL2_le_of_ae_bound hμ f p hε he)

end Polynomial.Sequence
