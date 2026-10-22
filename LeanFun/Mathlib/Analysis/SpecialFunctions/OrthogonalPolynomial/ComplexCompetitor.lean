/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ScalarCoefficients
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexSeries

/-!
# Complex Chebyshev competitors in arbitrary weighted L² spaces

Finite moments define the polynomial classes. The analytic error bound adds
only almost-everywhere support on [-1,1], allowing disconnected supports.
Reference: ATAP, Theorem 8.2 and Hilbert-space best approximation.
-/

public section
open Real Complex MeasureTheory Set
namespace Polynomial
variable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)

/-- The complex Chebyshev truncation, viewed in an arbitrary weighted L² space. -/
@[expose] noncomputable def complexChebyshevToL2 (F : Chebyshev.ComplexIntegrableInput) (N : ℕ) : Lp ℂ 2 μ :=
  ∑ n ∈ Finset.range (N + 1), Chebyshev.complexCoefficient (Chebyshev.ComplexCoefficientInput.ofL1 F n) •
    polynomialToL2Scalar ℂ hμ (Chebyshev.T ℝ n)

/-- The finite polynomial formula represents the weighted L² competitor. -/
theorem coe_complexChebyshevToL2 (F : Chebyshev.ComplexIntegrableInput) (N : ℕ) :
    complexChebyshevToL2 hμ F N =ᵐ[μ] fun x : ℝ ↦
      ∑ n ∈ Finset.range (N + 1), Chebyshev.complexCoefficient (Chebyshev.ComplexCoefficientInput.ofL1 F n) *
        (((Chebyshev.T ℝ n).eval x : ℝ) : ℂ) := by
  have hterm (n : ℕ) :
      (Chebyshev.complexCoefficient (Chebyshev.ComplexCoefficientInput.ofL1 F n) •
        polynomialToL2Scalar ℂ hμ (Chebyshev.T ℝ n) : Lp ℂ 2 μ) =ᵐ[μ]
      fun x : ℝ ↦ Chebyshev.complexCoefficient (Chebyshev.ComplexCoefficientInput.ofL1 F n) *
        (((Chebyshev.T ℝ n).eval x : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_smul (Chebyshev.complexCoefficient (Chebyshev.ComplexCoefficientInput.ofL1 F n))
      (polynomialToL2Scalar ℂ hμ (Chebyshev.T ℝ n)),
      coe_polynomialToL2Scalar ℂ hμ (Chebyshev.T ℝ n)] with x hs hp
    rw [hs]
    exact congrArg (fun z : ℂ ↦ Chebyshev.complexCoefficient (Chebyshev.ComplexCoefficientInput.ofL1 F n) * z) hp
  have hsum := eventuallyEq_sum (s := Finset.range (N + 1)) (fun n _ ↦ hterm n)
  apply (Lp.coeFn_finsetSum _ _).trans
  apply hsum.trans
  exact Filter.Eventually.of_forall (fun x ↦ by simp only [Finset.sum_apply])

/-- A degree-N complex Chebyshev competitor lies in the first N+1 scalar-extended
vectors of any nondegenerate polynomial sequence. -/
theorem complexChebyshevToL2_mem_span {P : Sequence ℝ}
    (hpos : HasPositiveDefiniteIntegral μ) (F : Chebyshev.ComplexIntegrableInput) (N : ℕ) :
    complexChebyshevToL2 hμ F N ∈ Submodule.span ℂ
      ((fun n ↦ P.normalizedToL2Scalar ℂ hμ ⟨n, Sequence.squaredNorm_pos hpos P n⟩) '' (Finset.range (N + 1) : Set ℕ)) := by
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  apply Sequence.polynomialToL2Scalar_mem_span ℂ hμ hpos N
  simp only [Chebyshev.degree_T, Int.natAbs_natCast, Nat.cast_le]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)

/-- The analytic complex competitor has weighted L² error at most square-root
mass times the usual geometric Chebyshev error. -/
theorem norm_sub_complexChebyshevToL2_le_of_analytic
    (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hF : AnalyticOnNhd ℂ F (bernsteinEllipse ⟨ρ, hρ⟩))
    (hM : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖F z‖ ≤ M)
    (f : Lp ℂ 2 μ) (hf : ∀ᵐ x ∂μ, f x = F x) (N : ℕ) :
    ‖f - complexChebyshevToL2 hμ ⟨(fun x : ℝ ↦ F x), Chebyshev.integrable_classicalMeasureT_complex (Chebyshev.continuousOn_real_of_analytic hρ hF)⟩ N‖ ≤
      √(μ.real univ) * (2 * M / (ρ ^ N * (ρ - 1))) := by
  let := hμ.isFiniteMeasure
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans
    (hM 0 (by simpa using (ofReal_mem_bernsteinEllipse hρ
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num))))
  have hb : ‖f - complexChebyshevToL2 hμ ⟨(fun x : ℝ ↦ F x), Chebyshev.integrable_classicalMeasureT_complex (Chebyshev.continuousOn_real_of_analytic hρ hF)⟩ N‖ ≤
      (measureUnivNNReal μ : ℝ) ^ (2 : ENNReal).toReal⁻¹ *
        (2 * M / (ρ ^ N * (ρ - 1))) := by
    apply Lp.norm_le_of_ae_bound (by positivity)
    filter_upwards [hf, hsupp, coe_complexChebyshevToL2 hμ ⟨(fun x : ℝ ↦ F x), Chebyshev.integrable_classicalMeasureT_complex (Chebyshev.continuousOn_real_of_analytic hρ hF)⟩ N,
      Lp.coeFn_sub f (complexChebyshevToL2 hμ ⟨(fun x : ℝ ↦ F x), Chebyshev.integrable_classicalMeasureT_complex (Chebyshev.continuousOn_real_of_analytic hρ hF)⟩ N)] with x hfx hx hp hsub
    rw [hsub]
    simp only [Pi.sub_apply, hfx, hp]
    exact Chebyshev.norm_sub_sum_complexCoefficient_le_of_analytic hρ hF hM hx N
  norm_num only [ENNReal.toReal_ofNat] at hb
  simpa only [Real.sqrt_eq_rpow, one_div, measureUnivNNReal, Measure.real, ENNReal.toReal] using hb

/-- The scalar-extended reproducing kernel evaluates the complex competitor. -/
theorem Sequence.IsOrthogonal.inner_kernelVectorScalar_complexChebyshevToL2
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (hpos : HasPositiveDefiniteIntegral μ)
    (F : Chebyshev.ComplexIntegrableInput) (N : ℕ) (x : ℝ) :
    inner ℂ (P.kernelVectorScalar ℂ hμ ⟨N, fun i _ ↦ Sequence.squaredNorm_pos hpos P i⟩ x) (complexChebyshevToL2 hμ F N) =
      ∑ n ∈ Finset.range (N + 1), Chebyshev.complexCoefficient (Chebyshev.ComplexCoefficientInput.ofL1 F n) *
        (((Chebyshev.T ℝ n).eval x : ℝ) : ℂ) := by
  rw [complexChebyshevToL2, inner_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hdeg : (Chebyshev.T ℝ (n : ℤ)).degree ≤ N := by
    simp only [Chebyshev.degree_T, Int.natAbs_natCast, Nat.cast_le]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  rw [inner_smul_right,
    hP.inner_kernelVectorScalar_polynomialToL2Scalar ℂ hμ hpos N x _ hdeg]
  rfl

end Polynomial
