/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ScalarExtension
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.KernelBound

/-!
# Integral coefficients and reproducing kernels after scalar extension

The real polynomial normalization is unchanged for complex-valued data.
Reference: DLMF 18.2(v), (viii).
-/

public section
open MeasureTheory Real
open scoped InnerProductSpace
namespace Polynomial.Sequence
variable (𝕂 : Type*) [RCLike 𝕂] {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
variable (P : Sequence ℝ)

/-- Integral coefficients over real or complex scalars, for a real polynomial family. -/
@[expose] noncomputable def integralCoefficientScalar (μ : Measure ℝ) {n : ℕ}
    (f : IntegralCoefficientInput 𝕂 μ (P n)) : 𝕂 :=
  (P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _ (by simpa only [pow_two] using f.square_integrable)) : 𝕂)⁻¹ *
    ∫ x, f.val x * (((P n).eval x : ℝ) : 𝕂) ∂μ

/-- The classical scalar coefficient formula (DLMF 18.2(viii)). -/
theorem integralCoefficientScalar_apply (μ : Measure ℝ) {n : ℕ}
    (f : IntegralCoefficientInput 𝕂 μ (P n)) :
    P.integralCoefficientScalar 𝕂 μ f = ((∫ x, (P n).eval x ^ 2 ∂μ : ℝ) : 𝕂)⁻¹ *
      ∫ x, f.val x * (((P n).eval x : ℝ) : 𝕂) ∂μ := by
  simp only [integralCoefficientScalar, squaredNorm, integralInner_self]

/-- Pointwise evaluation of a finite classical scalar-valued expansion. -/
@[expose] noncomputable def partialSumValueScalar (μ : Measure ℝ) {N : ℕ}
    (f : IntegralCoefficientFamilyInput 𝕂 μ P N) (x : ℝ) : 𝕂 :=
  ∑ i : Fin (N + 1), P.integralCoefficientScalar 𝕂 μ (f.at i) * (((P i).eval x : ℝ) : 𝕂)

/-- The finite scalar formula on its classical input domain. -/
theorem partialSumValueScalar_apply (μ : Measure ℝ) {N : ℕ}
    (f : IntegralCoefficientFamilyInput 𝕂 μ P N) (x : ℝ) :
    P.partialSumValueScalar 𝕂 μ f x =
      ∑ i : Fin (N + 1), P.integralCoefficientScalar 𝕂 μ (f.at i) * (((P i).eval x : ℝ) : 𝕂) := rfl

/-- Internal range-indexed formula for L2 data. -/
theorem partialSumValueScalar_ofL2 (hpos : HasPositiveDefiniteIntegral μ)
    (f : Lp 𝕂 2 μ) (N : ℕ) (x : ℝ) :
    P.partialSumValueScalar 𝕂 μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N) x =
      ∑ i ∈ Finset.range (N + 1), P.integralCoefficientScalar 𝕂 μ
        (IntegralCoefficientInput.ofL2 hμ hpos (P i) (P.ne_zero i) f) * (((P i).eval x : ℝ) : 𝕂) := by
  simp only [partialSumValueScalar, IntegralCoefficientFamilyInput.ofL2_at]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ P.integralCoefficientScalar 𝕂 μ
    (IntegralCoefficientInput.ofL2 hμ hpos (P i) (P.ne_zero i) f) * (((P i).eval x : ℝ) : 𝕂)) (N + 1)

/-- Scalar extension of the real Christoffel evaluation vector. -/
@[expose] noncomputable def kernelVectorScalar (N : {N : ℕ // ∀ i ≤ N, 0 < P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)}) (x : ℝ) : Lp 𝕂 2 μ :=
  (@RCLike.ofRealCLM 𝕂 _).compLp (P.kernelVector hμ N x)

/-- Scalar embedding of the classical finite kernel vector (DLMF 18.2(v)). -/
theorem kernelVectorScalar_apply
    (N : {N : ℕ // ∀ i ≤ N, 0 < P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)}) (x : ℝ) :
    P.kernelVectorScalar 𝕂 hμ N x =
      (@RCLike.ofRealCLM 𝕂 _).compLp (P.kernelVector hμ N x) := rfl

variable {P}

/-- Normalized inner-product coordinates rescale to the integral coefficient. -/
theorem inner_normalizedToL2Scalar_mul_inv_sqrt (hpos : HasPositiveDefiniteIntegral μ)
    (f : Lp 𝕂 2 μ) (n : ℕ) :
    inner 𝕂 (P.normalizedToL2Scalar 𝕂 hμ ⟨n, squaredNorm_pos hpos P n⟩) f * (((√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ : ℝ) : 𝕂) =
      P.integralCoefficientScalar 𝕂 μ (IntegralCoefficientInput.ofL2 hμ hpos (P n) (P.ne_zero n) f) := by
  rw [normalizedToL2Scalar_eq, inner_smul_left, inner_polynomialToL2Scalar_left]
  simp only [RCLike.conj_ofReal]
  calc
    _ = ((((√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ * (√(P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ : ℝ) : 𝕂)) *
        (∫ x, f x * (((P n).eval x : ℝ) : 𝕂) ∂μ) := by
      rw [RCLike.ofReal_mul]
      ring
    _ = _ := by
      rw [← mul_inv, Real.mul_self_sqrt (squaredNorm_pos hpos P n).le,
        RCLike.ofReal_inv]
      rfl

/-- Integral-coefficient terms represent the finite orthonormal projection. -/
theorem inner_normalizedToL2Scalar_smul (hpos : HasPositiveDefiniteIntegral μ)
    (f : Lp 𝕂 2 μ) (n : ℕ) :
    inner 𝕂 (P.normalizedToL2Scalar 𝕂 hμ ⟨n, squaredNorm_pos hpos P n⟩) f • P.normalizedToL2Scalar 𝕂 hμ ⟨n, squaredNorm_pos hpos P n⟩ =
      P.integralCoefficientScalar 𝕂 μ (IntegralCoefficientInput.ofL2 hμ hpos (P n) (P.ne_zero n) f) • polynomialToL2Scalar 𝕂 hμ (P n) := by
  rw [normalizedToL2Scalar_eq 𝕂 hμ P ⟨n, squaredNorm_pos hpos P n⟩, smul_smul]
  congr 1
  simpa only [normalizedToL2Scalar_eq] using
    (inner_normalizedToL2Scalar_mul_inv_sqrt 𝕂 hμ (P := P) hpos f n)

/-- The scalar-extended kernel vector reproduces partial-sum evaluation. -/
theorem inner_kernelVectorScalar (hpos : HasPositiveDefiniteIntegral μ)
    (N : ℕ) (x : ℝ) (f : Lp 𝕂 2 μ) :
    inner 𝕂 (P.kernelVectorScalar 𝕂 hμ ⟨N, fun i _ ↦ squaredNorm_pos hpos P i⟩ x) f = P.partialSumValueScalar 𝕂 μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N) x := by
  rw [kernelVectorScalar, kernelVector_of_positive hμ P hpos]
  change inner 𝕂 (((@RCLike.ofRealCLM 𝕂 _).compLpₗ 2 μ)
    (∑ i ∈ Finset.range (N + 1), ((P i).eval x / √(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _))) •
      P.normalizedToL2 hμ ⟨i, squaredNorm_pos hpos P i⟩)) f = _
  simp only [map_sum, map_smul, sum_inner,
    RCLike.real_smul_eq_coe_smul (K := 𝕂), inner_smul_left, RCLike.conj_ofReal,
    partialSumValueScalar_ofL2]
  apply Finset.sum_congr rfl
  intro i _
  change (((P i).eval x / √(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)) : ℝ) : 𝕂) *
    inner 𝕂 (P.normalizedToL2Scalar 𝕂 hμ ⟨i, squaredNorm_pos hpos P i⟩) f = _
  rw [div_eq_mul_inv, RCLike.ofReal_mul]
  calc
    _ = (inner 𝕂 (P.normalizedToL2Scalar 𝕂 hμ ⟨i, squaredNorm_pos hpos P i⟩) f *
        (((√(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ : ℝ) : 𝕂)) * (((P i).eval x : ℝ) : 𝕂) := by ring
    _ = _ := by rw [inner_normalizedToL2Scalar_mul_inv_sqrt 𝕂 hμ hpos]

/-- Scalar extension leaves the norm of the Christoffel kernel vector unchanged. -/
theorem IsOrthogonal.norm_kernelVectorScalar (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (N : ℕ) (x : ℝ) :
    ‖P.kernelVectorScalar 𝕂 hμ ⟨N, fun i _ ↦ squaredNorm_pos hpos P i⟩ x‖ = √(P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _)) := by
  rw [kernelVectorScalar, norm_ofReal_compLp, hP.norm_kernelVector hμ hpos]

/-- The scalar kernel reproduces every real polynomial of degree at most N. -/
theorem IsOrthogonal.inner_kernelVectorScalar_polynomialToL2Scalar (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (N : ℕ) (x : ℝ)
    (p : ℝ[X]) (hp : p.degree ≤ N) :
    inner 𝕂 (P.kernelVectorScalar 𝕂 hμ ⟨N, fun i _ ↦ squaredNorm_pos hpos P i⟩ x) (polynomialToL2Scalar 𝕂 hμ p) =
      ((p.eval x : ℝ) : 𝕂) := by
  change inner 𝕂 ((@RCLike.ofRealCLM 𝕂 _).compLp _) ((@RCLike.ofRealCLM 𝕂 _).compLp _) = _
  rw [inner_ofReal_compLp, inner_kernelVector hμ hpos,
    hP.partialSum_polynomialToL2 hμ hpos N p hp]

end Polynomial.Sequence
