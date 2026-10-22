/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.HilbertBasis
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.CoefficientInput

/-! # Gegenbauer Hilbert bases and L² expansions
Compact support supplies polynomial density, and the general orthogonal
sequence construction supplies the Hilbert basis. Reference: DLMF 18.2(viii).
-/
public section
open MeasureTheory Real Filter
namespace Polynomial
variable {lam : ℝ} (hlam : -(1 / 2) < lam) (hzero : lam ≠ 0)

/-- Gegenbauer polynomial classes are dense in weighted L² (DLMF 18.2(viii)). -/
theorem polynomialToL2_gegenbauer_denseRange :
    DenseRange (polynomialToL2 (hasFiniteMoments_gegenbauerMeasure hlam)) :=
  polynomialToL2_denseRange (hasFiniteMoments_gegenbauerMeasure hlam) (-1) 1
    ((ae_mem_Ioo_gegenbauerMeasure lam).mono (fun _ hx ↦ Set.Ioo_subset_Icc_self hx))

/-- The general squared norm is the Gegenbauer squared integral (DLMF Table 18.3.1). -/
theorem squaredNorm_gegenbauerSequence (n : ℕ) :
    (gegenbauerSequence hlam hzero).squaredNorm (gegenbauerMeasure lam) n (Polynomial.Sequence.IntegrableSquare.of _ _) =
      ∫ x, (gegenbauer lam n).eval x ^ 2 ∂gegenbauerMeasure lam := by
  simp only [Sequence.squaredNorm, integralInner_self, gegenbauerSequence_apply]

/-- Normalised Gegenbauer classes (DLMF Table 18.3.1). -/
noncomputable def normalizedGegenbauer (n : ℕ) : Lp ℝ 2 (gegenbauerMeasure lam) :=
  (gegenbauerSequence hlam hzero).normalizedToL2 (hasFiniteMoments_gegenbauerMeasure hlam) ⟨n, Sequence.squaredNorm_pos (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) (gegenbauerSequence hlam hzero) n⟩

/-- The usual positive square-root normalisation (DLMF Table 18.3.1). -/
theorem normalizedGegenbauer_eq (n : ℕ) :
    normalizedGegenbauer hlam hzero n =
      (√(∫ x, (gegenbauer lam n).eval x ^ 2 ∂gegenbauerMeasure lam))⁻¹ •
        polynomialToL2 (hasFiniteMoments_gegenbauerMeasure hlam) (gegenbauer lam n) := by
  simp only [normalizedGegenbauer, Sequence.normalizedToL2, squaredNorm_gegenbauerSequence,
    gegenbauerSequence_apply]

/-- The normalised Gegenbauer family is orthonormal (DLMF 18.2(viii)). -/
theorem orthonormal_normalizedGegenbauer : Orthonormal ℝ (normalizedGegenbauer hlam hzero) :=
  (isOrthogonal_gegenbauerSequence hlam hzero).orthonormal_normalizedToL2
    (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)

/-- The Gegenbauer Hilbert basis (DLMF 18.2(viii)). -/
noncomputable def hilbertBasisGegenbauer : HilbertBasis ℕ ℝ (Lp ℝ 2 (gegenbauerMeasure lam)) :=
  (isOrthogonal_gegenbauerSequence hlam hzero).hilbertBasis
    (hasFiniteMoments_gegenbauerMeasure hlam)
    (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) (polynomialToL2_gegenbauer_denseRange hlam)

/-- The Hilbert basis vectors are the normalised Gegenbauer classes (DLMF 18.2(viii)). -/
@[simp] theorem hilbertBasisGegenbauer_apply (n : ℕ) :
    hilbertBasisGegenbauer hlam hzero n = normalizedGegenbauer hlam hzero n :=
  (isOrthogonal_gegenbauerSequence hlam hzero).hilbertBasis_apply
    (hasFiniteMoments_gegenbauerMeasure hlam)
    (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)
    (polynomialToL2_gegenbauer_denseRange hlam) n

/-- L2 data in the classical Gegenbauer range supply every coefficient input
(DLMF 18.2(viii)). -/
@[expose] noncomputable def IntegralCoefficientInput.ofGegenbauerL2 {𝕂 : Type*} [RCLike 𝕂]
    (f : Lp 𝕂 2 (gegenbauerMeasure lam)) (n : ℕ) :
    IntegralCoefficientInput 𝕂 (gegenbauerMeasure lam) (gegenbauer lam n) :=
  IntegralCoefficientInput.ofL2 (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)
    (gegenbauer lam n) (by simpa only [gegenbauerSequence_apply] using (gegenbauerSequence hlam hzero).ne_zero n) f

/-- Gegenbauer integral coefficients on their full classical domain (DLMF 18.2(viii)). -/
@[expose] noncomputable def gegenbauerCoefficient (lam : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℝ (gegenbauerMeasure lam) (gegenbauer lam n)) : ℝ :=
  (∫ x, (gegenbauer lam n).eval x ^ 2 ∂gegenbauerMeasure lam)⁻¹ *
    ∫ x, f.val x * (gegenbauer lam n).eval x ∂gegenbauerMeasure lam

/-- The classical weighted formula includes its integrability and positive normalization. -/
theorem gegenbauerCoefficient_apply (lam : ℝ) {n : ℕ}
    (f : IntegralCoefficientInput ℝ (gegenbauerMeasure lam) (gegenbauer lam n)) :
    gegenbauerCoefficient lam f =
      (∫ x, (gegenbauer lam n).eval x ^ 2 ∂gegenbauerMeasure lam)⁻¹ *
        ∫ x, f.val x * (gegenbauer lam n).eval x ∂gegenbauerMeasure lam := rfl

/-- The generic integral coefficients are the Gegenbauer coefficients on the
classical input domain (DLMF 18.2(viii)). -/
theorem integralCoefficient_gegenbauerSequence {n : ℕ}
    (f : IntegralCoefficientInput ℝ (gegenbauerMeasure lam) (gegenbauer lam n)) :
    (gegenbauerSequence hlam hzero).integralCoefficient (gegenbauerMeasure lam) f =
      gegenbauerCoefficient lam f := by
  simp only [Sequence.integralCoefficient, squaredNorm_gegenbauerSequence,
    gegenbauerSequence_apply, gegenbauerCoefficient]

/-- Internal specialization for L2 representatives. -/
theorem integralCoefficient_gegenbauerSequence_L2 (f : Lp ℝ 2 (gegenbauerMeasure lam)) (n : ℕ) :
    (gegenbauerSequence hlam hzero).integralCoefficient (gegenbauerMeasure lam) (IntegralCoefficientInput.ofL2 (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) ((gegenbauerSequence hlam hzero) n) ((gegenbauerSequence hlam hzero).ne_zero n) f) =
      gegenbauerCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f n) := by
  simp only [Sequence.integralCoefficient, squaredNorm_gegenbauerSequence,
    gegenbauerSequence_apply, gegenbauerCoefficient, IntegralCoefficientInput.ofGegenbauerL2,
    IntegralCoefficientInput.ofL2]

include hzero

/-- Every weighted L² function is the sum of its Gegenbauer series in L² (DLMF 18.2(viii)). -/
theorem hasSum_gegenbauerCoefficient_polynomialToL2 (f : Lp ℝ 2 (gegenbauerMeasure lam)) :
    HasSum (fun n ↦ (gegenbauerCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f n)) •
      polynomialToL2 (hasFiniteMoments_gegenbauerMeasure hlam) (gegenbauer lam n)) f := by
  simpa only [Sequence.integralCoefficient, squaredNorm_gegenbauerSequence, gegenbauerSequence_apply,
    gegenbauerCoefficient, IntegralCoefficientInput.ofGegenbauerL2, IntegralCoefficientInput.ofL2] using
    (isOrthogonal_gegenbauerSequence hlam hzero).hasSum_integralCoefficient
      (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)
      (polynomialToL2_gegenbauer_denseRange hlam) f

/-- Natural-order Gegenbauer partial sums converge in L² (DLMF 18.2(viii)). -/
theorem tendsto_sum_gegenbauerCoefficient_polynomialToL2 (f : Lp ℝ 2 (gegenbauerMeasure lam)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, (gegenbauerCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f n)) •
      polynomialToL2 (hasFiniteMoments_gegenbauerMeasure hlam) (gegenbauer lam n)) atTop (nhds f) :=
  (hasSum_gegenbauerCoefficient_polynomialToL2 hlam hzero f).tendsto_sum_nat

end Polynomial
