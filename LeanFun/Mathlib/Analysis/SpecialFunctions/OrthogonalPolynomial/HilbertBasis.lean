/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.CoefficientInput
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.RecurrenceCoefficients
import Mathlib.Tactic.Ring

/-! # Hilbert bases from complete orthogonal polynomial sequences
Density is an explicit hypothesis. No interval-support condition is imposed.
Reference: DLMF 18.2(viii).
-/
public section
open Real MeasureTheory
open scoped InnerProductSpace
namespace Polynomial.Sequence
variable {μ : Measure ℝ} (P : Sequence ℝ) (hμ : HasFiniteMoments μ)

/-- Normalised polynomial classes in weighted L² (DLMF 18.2(viii)). -/
@[expose] noncomputable def normalizedToL2 (n : {n : ℕ // 0 < P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)}) : Lp ℝ 2 μ :=
  (√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ • polynomialToL2 hμ (P n)

/-- Classical positive-norm normalization formula (DLMF 18.2(viii)). -/
theorem normalizedToL2_apply (n : {n : ℕ // 0 < P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)}) :
    P.normalizedToL2 hμ n =
      (√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ • polynomialToL2 hμ (P n) := rfl

variable {P}

/-- Normalising an orthogonal sequence gives an orthonormal family (DLMF 18.2(viii)). -/
theorem IsOrthogonal.orthonormal_normalizedToL2 (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) : Orthonormal ℝ (fun n ↦ P.normalizedToL2 hμ ⟨n, squaredNorm_pos hpos P n⟩) := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalizedToL2, inner_smul_left, inner_smul_right, conj_trivial,
    inner_polynomialToL2]
  by_cases h : n = m
  · subst m
    simp only [↓reduceIte]
    have hp := squaredNorm_pos hpos P n
    have hn : (∫ x, (P n).eval x * (P n).eval x ∂μ) = P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _) := rfl
    rw [hn]
    calc
      _ = ((√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ * (√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹) * P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _) := by ring
      _ = 1 := by rw [← mul_inv, Real.mul_self_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  · rw [hP.orthogonal n m h]
    simp [h]

variable (P)

/-- Polynomial-sequence vectors span all polynomial classes (DLMF 18.2(viii)). -/
theorem span_polynomialToL2 :
    Submodule.span ℝ (Set.range (fun n ↦ polynomialToL2 hμ (P n))) =
      LinearMap.range (polynomialToL2 hμ) := by
  have hs : Submodule.span ℝ (Set.range P) = ⊤ := by
    apply P.span
    intro n
    exact P.isUnit_leadingCoeff n
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def, Submodule.map_top]
    using congrArg (Submodule.map (polynomialToL2 hμ)) hs

/-- Density of polynomial classes implies density of their normalised span (DLMF 18.2(viii)). -/
theorem normalizedToL2_dense_span (hpos : HasPositiveDefiniteIntegral μ)
    (hdense : DenseRange (polynomialToL2 hμ)) :
    (Submodule.span ℝ (Set.range (fun n ↦ P.normalizedToL2 hμ ⟨n, squaredNorm_pos hpos P n⟩))).topologicalClosure = ⊤ := by
  have hd : (Submodule.span ℝ (Set.range (fun n ↦ polynomialToL2 hμ (P n)))).topologicalClosure = ⊤ := by
    rw [P.span_polynomialToL2]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
  have hs : Submodule.span ℝ (Set.range (fun n ↦ polynomialToL2 hμ (P n))) ≤
      Submodule.span ℝ (Set.range (fun n ↦ P.normalizedToL2 hμ ⟨n, squaredNorm_pos hpos P n⟩)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    have hz : √(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)) ≠ 0 := (Real.sqrt_pos.mpr (squaredNorm_pos hpos P n)).ne'
    have hm := (Submodule.span ℝ (Set.range (fun n ↦ P.normalizedToL2 hμ ⟨n, squaredNorm_pos hpos P n⟩))).smul_mem
      (√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _))) (Submodule.subset_span (Set.mem_range_self n))
    simpa only [SetLike.mem_coe, normalizedToL2, smul_smul, mul_inv_cancel₀ hz, one_smul] using hm
  apply top_unique
  rw [← hd]
  exact Submodule.topologicalClosure_mono hs

variable {P}

/-- The Hilbert basis associated with a complete orthogonal polynomial sequence (DLMF 18.2(viii)). -/
noncomputable def IsOrthogonal.hilbertBasis (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (hdense : DenseRange (polynomialToL2 hμ)) :
    HilbertBasis ℕ ℝ (Lp ℝ 2 μ) :=
  HilbertBasis.mk (hP.orthonormal_normalizedToL2 hμ hpos)
    (by rw [P.normalizedToL2_dense_span hμ hpos hdense])

/-- The Hilbert basis vectors use positive square-root normalisation (DLMF 18.2(viii)). -/
@[simp] theorem IsOrthogonal.hilbertBasis_apply (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (hdense : DenseRange (polynomialToL2 hμ)) (n : ℕ) :
    hP.hilbertBasis hμ hpos hdense n = P.normalizedToL2 hμ ⟨n, squaredNorm_pos hpos P n⟩ := by
  exact congrFun (HilbertBasis.coe_mk _ _) n

variable (P)

/-- Integral coefficients for the original, unnormalised polynomial sequence (DLMF 18.2(viii)). -/
@[expose] noncomputable def integralCoefficient (μ : Measure ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℝ μ (P n)) : ℝ :=
  (P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _ (by simpa only [pow_two] using f.square_integrable)))⁻¹ *
    ∫ x, f.val x * (P n).eval x ∂μ

/-- The normalized integral formula on its classical input domain (DLMF 18.2(viii)). -/
theorem integralCoefficient_apply (μ : Measure ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℝ μ (P n)) :
    P.integralCoefficient μ f = (∫ x, (P n).eval x ^ 2 ∂μ)⁻¹ *
      ∫ x, f.val x * (P n).eval x ∂μ := by
  simp only [integralCoefficient, squaredNorm, integralInner_self]


variable {P}

/-- Hilbert-coordinate terms equal the integral-coefficient terms (DLMF 18.2(viii)). -/
theorem IsOrthogonal.hilbertBasis_repr_smul (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (hdense : DenseRange (polynomialToL2 hμ))
    (f : Lp ℝ 2 μ) (n : ℕ) :
    (hP.hilbertBasis hμ hpos hdense).repr f n • hP.hilbertBasis hμ hpos hdense n =
      P.integralCoefficient μ (IntegralCoefficientInput.ofL2 hμ hpos (P n) (P.ne_zero n) f) • polynomialToL2 hμ (P n) := by
  rw [HilbertBasis.repr_apply_apply, IsOrthogonal.hilbertBasis_apply, normalizedToL2,
    inner_smul_left, inner_polynomialToL2_left]
  simp only [conj_trivial, smul_smul]
  congr 1
  calc
    _ = ((√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ * (√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹) *
        (∫ x, f x * (P n).eval x ∂μ) := by ring
    _ = _ := by rw [← mul_inv, Real.mul_self_sqrt (squaredNorm_pos hpos P n).le]; rfl

/-- Integral-coefficient expansions sum in L² (DLMF 18.2(viii)). -/
theorem IsOrthogonal.hasSum_integralCoefficient (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (hdense : DenseRange (polynomialToL2 hμ))
    (f : Lp ℝ 2 μ) :
    HasSum (fun n ↦ P.integralCoefficient μ (IntegralCoefficientInput.ofL2 hμ hpos (P n) (P.ne_zero n) f) • polynomialToL2 hμ (P n)) f := by
  simpa only [hP.hilbertBasis_repr_smul hμ hpos hdense] using
    (hP.hilbertBasis hμ hpos hdense).hasSum_repr f

end Polynomial.Sequence
