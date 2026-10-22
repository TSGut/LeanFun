/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Norm
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.HilbertBasis
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.CoefficientInput

/-! # Jacobi Hilbert bases and L² expansions
Compact support supplies polynomial density, and the general orthogonal
sequence construction supplies the Hilbert basis. Reference: DLMF 18.2(viii).
-/
public section
open MeasureTheory Real Filter
namespace Polynomial
variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)

/-- Jacobi polynomial classes are dense in weighted L² (DLMF 18.2(viii)). -/
theorem polynomialToL2_jacobi_denseRange :
    DenseRange (polynomialToL2 (hasFiniteMoments_jacobiMeasure hα hβ)) :=
  polynomialToL2_denseRange (hasFiniteMoments_jacobiMeasure hα hβ) (-1) 1
    ((ae_mem_Ioo_jacobiMeasure α β).mono (fun _ hx ↦ Set.Ioo_subset_Icc_self hx))

/-- The general squared norm is the Jacobi squared integral (DLMF Table 18.3.1). -/
theorem squaredNorm_jacobiSequence (n : ℕ) :
    (jacobiSequence hα hβ).squaredNorm (jacobiMeasure α β) n (Polynomial.Sequence.IntegrableSquare.of _ _) =
      ∫ x, (jacobi α β n).eval x ^ 2 ∂jacobiMeasure α β := by
  simp only [Sequence.squaredNorm, integralInner_self, jacobiSequence_apply]

/-- Normalised Jacobi classes (DLMF Table 18.3.1). -/
noncomputable def normalizedJacobi (n : ℕ) : Lp ℝ 2 (jacobiMeasure α β) :=
  (jacobiSequence hα hβ).normalizedToL2 (hasFiniteMoments_jacobiMeasure hα hβ) ⟨n, Sequence.squaredNorm_pos (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) (jacobiSequence hα hβ) n⟩

/-- The usual positive square-root normalisation (DLMF Table 18.3.1). -/
theorem normalizedJacobi_eq (n : ℕ) :
    normalizedJacobi hα hβ n =
      (√(∫ x, (jacobi α β n).eval x ^ 2 ∂jacobiMeasure α β))⁻¹ •
        polynomialToL2 (hasFiniteMoments_jacobiMeasure hα hβ) (jacobi α β n) := by
  simp only [normalizedJacobi, Sequence.normalizedToL2, squaredNorm_jacobiSequence, jacobiSequence_apply]

/-- The normalised Jacobi family is orthonormal (DLMF 18.2(viii)). -/
theorem orthonormal_normalizedJacobi : Orthonormal ℝ (normalizedJacobi hα hβ) :=
  (isOrthogonal_jacobiSequence hα hβ).orthonormal_normalizedToL2
    (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)

/-- The Jacobi Hilbert basis (DLMF 18.2(viii)). -/
noncomputable def hilbertBasisJacobi : HilbertBasis ℕ ℝ (Lp ℝ 2 (jacobiMeasure α β)) :=
  (isOrthogonal_jacobiSequence hα hβ).hilbertBasis (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) (polynomialToL2_jacobi_denseRange hα hβ)

/-- The Hilbert basis vectors are the normalised Jacobi classes (DLMF 18.2(viii)). -/
@[simp] theorem hilbertBasisJacobi_apply (n : ℕ) :
    hilbertBasisJacobi hα hβ n = normalizedJacobi hα hβ n :=
  (isOrthogonal_jacobiSequence hα hβ).hilbertBasis_apply (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) (polynomialToL2_jacobi_denseRange hα hβ) n

/-- L2 data in the classical Jacobi range supply every coefficient input
(DLMF 18.2(viii)). -/
@[expose] noncomputable def IntegralCoefficientInput.ofJacobiL2 {𝕂 : Type*} [RCLike 𝕂]
    (f : Lp 𝕂 2 (jacobiMeasure α β)) (n : ℕ) :
    IntegralCoefficientInput 𝕂 (jacobiMeasure α β) (jacobi α β n) :=
  IntegralCoefficientInput.ofL2 (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)
    (jacobi α β n) (by simpa only [jacobiSequence_apply] using (jacobiSequence hα hβ).ne_zero n) f

/-- Jacobi integral coefficients on their full classical domain (DLMF 18.2(viii)). -/
@[expose] noncomputable def jacobiCoefficient (α β : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℝ (jacobiMeasure α β) (jacobi α β n)) : ℝ :=
  (∫ x, (jacobi α β n).eval x ^ 2 ∂jacobiMeasure α β)⁻¹ *
    ∫ x, f.val x * (jacobi α β n).eval x ∂jacobiMeasure α β

/-- The classical weighted formula includes its integrability and positive normalization. -/
theorem jacobiCoefficient_apply (α β : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℝ (jacobiMeasure α β) (jacobi α β n)) :
    jacobiCoefficient α β f =
      (∫ x, (jacobi α β n).eval x ^ 2 ∂jacobiMeasure α β)⁻¹ *
        ∫ x, f.val x * (jacobi α β n).eval x ∂jacobiMeasure α β := rfl

/-- The generic integral coefficients are the Jacobi coefficients on the
classical input domain (DLMF 18.2(viii)). -/
theorem integralCoefficient_jacobiSequence {n : ℕ}
    (f : IntegralCoefficientInput ℝ (jacobiMeasure α β) (jacobi α β n)) :
    (jacobiSequence hα hβ).integralCoefficient (jacobiMeasure α β) f =
      jacobiCoefficient α β f := by
  simp only [Sequence.integralCoefficient, squaredNorm_jacobiSequence,
    jacobiSequence_apply, jacobiCoefficient]

/-- Internal specialization for L2 representatives. -/
theorem integralCoefficient_jacobiSequence_L2 (f : Lp ℝ 2 (jacobiMeasure α β)) (n : ℕ) :
    (jacobiSequence hα hβ).integralCoefficient (jacobiMeasure α β) (IntegralCoefficientInput.ofL2 (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) ((jacobiSequence hα hβ) n) ((jacobiSequence hα hβ).ne_zero n) f) =
      jacobiCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f n) := by
  simp only [Sequence.integralCoefficient, squaredNorm_jacobiSequence,
    jacobiSequence_apply, jacobiCoefficient, IntegralCoefficientInput.ofJacobiL2,
    IntegralCoefficientInput.ofL2]

/-- Every weighted L² function is the sum of its Jacobi series in L² (DLMF 18.2(viii)). -/
theorem hasSum_jacobiCoefficient_polynomialToL2 (f : Lp ℝ 2 (jacobiMeasure α β)) :
    HasSum (fun n ↦ (jacobiCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f n)) •
      polynomialToL2 (hasFiniteMoments_jacobiMeasure hα hβ) (jacobi α β n)) f := by
  simpa only [Sequence.integralCoefficient, squaredNorm_jacobiSequence, jacobiSequence_apply,
    jacobiCoefficient, IntegralCoefficientInput.ofJacobiL2, IntegralCoefficientInput.ofL2] using
    (isOrthogonal_jacobiSequence hα hβ).hasSum_integralCoefficient
      (hasFiniteMoments_jacobiMeasure hα hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ)
      (polynomialToL2_jacobi_denseRange hα hβ) f

/-- Natural-order Jacobi partial sums converge in L² (DLMF 18.2(viii)). -/
theorem tendsto_sum_jacobiCoefficient_polynomialToL2 (f : Lp ℝ 2 (jacobiMeasure α β)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, (jacobiCoefficient α β (IntegralCoefficientInput.ofJacobiL2 hα hβ f n)) •
      polynomialToL2 (hasFiniteMoments_jacobiMeasure hα hβ) (jacobi α β n)) atTop (nhds f) :=
  (hasSum_jacobiCoefficient_polynomialToL2 hα hβ f).tendsto_sum_nat

end Polynomial
