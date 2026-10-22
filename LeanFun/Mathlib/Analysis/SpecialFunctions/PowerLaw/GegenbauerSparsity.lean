/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerKernel
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionSupport

/-! # Symmetry and exact bandwidth of compatible power-law operators

Fubini turns symmetry of the kernel into weighted symmetry of the coefficient
operator. Together with polynomial degree growth this proves both sides of the
band, without truncation or numerical zero thresholds.
Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

public section
open Polynomial Set MeasureTheory Filter
open scoped ENNReal NNReal
namespace Real

/-- The exact polynomial operator is symmetric for the Gegenbauer inner product. -/
theorem integralInner_powerLawGegenbauerOperator_comm {α lam : ℝ} {k : ℕ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hzero : lam ≠ 0) (hk : lam+α/2 = k)
    (p q : ℝ[X]) :
    integralInner (gegenbauerMeasure lam) (IntegrablePair.of (gegenbauerMeasure lam) (powerLawGegenbauerOperator (.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩ hzero) k p) q) =
      integralInner (gegenbauerMeasure lam) (IntegrablePair.of (gegenbauerMeasure lam) (powerLawGegenbauerOperator (.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩ hzero) k q) p) := by
  let := isFiniteMeasure_gegenbauerMeasure hlam
  have he (p q : ℝ[X]) :
      integralInner (gegenbauerMeasure lam) (IntegrablePair.of (gegenbauerMeasure lam)
        (powerLawGegenbauerOperator (.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩ hzero) k p) q) =
      ∫ z : ℝ × ℝ, q.eval z.1*p.eval z.2 ∂powerLawKernelMeasure α lam := by
    obtain ⟨F,hF,hI⟩ := powerLawWeakFubini (fun y ↦ p.eval y) (fun x ↦ q.eval x)
      (integrable_powerLawKernelMeasure_polynomial_of_compatible hα hlam hk p q)
    rw [← hI]
    unfold integralInner
    apply integral_congr_ae
    filter_upwards [ae_mem_Ioo_gegenbauerMeasure lam,hF] with x hx hFx
    obtain ⟨I,hval,hFI⟩ := hFx
    rw [hFI,eval_powerLawGegenbauerOperator ⟨α,hα⟩ ⟨lam,hlam⟩ hzero hk ⟨x,hx⟩ p,
      powerLawPolynomial_apply]
    unfold powerLawIntegral
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hval y,PowerLawInput.gegenbauerPolynomial_apply]
    ring
  rw [he,he]
  obtain ⟨K,hK,hKe,hz,hμ⟩ := exists_powerLawKernel_density α
  have hsym (z : ℝ × ℝ) : K z.swap = K z := by
    by_cases h : z.1 ∈ Ioo (-1 : ℝ) 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 1 ∧ z.1 ≠ z.2
    · apply NNReal.eq
      rw [hKe ⟨z,h⟩,hKe ⟨z.swap,h.2.1,h.1,h.2.2.symm⟩]
      change |z.2-z.1|^α = |z.1-z.2|^α
      rw [abs_sub_comm]
    · rw [hz z h,hz z.swap (fun hs ↦ h ⟨hs.2.1,hs.1,hs.2.2.symm⟩)]
  have hm : powerLawKernelMeasure α lam =
      ((gegenbauerMeasure lam).prod (gegenbauerMeasure lam)).withDensity
        (fun z ↦ (K z : ℝ≥0∞)) := hμ lam lam
  rw [hm,integral_withDensity_eq_integral_toReal_smul hK.coe_nnreal_ennreal (by simp),
    integral_withDensity_eq_integral_toReal_smul hK.coe_nnreal_ennreal (by simp)]
  rw [← integral_prod_swap]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [ENNReal.coe_toReal,smul_eq_mul,Prod.swap,mul_comm]
  rw [show K (z.2,z.1) = K z from hsym z]
  ring

/-- Both sides of the compatibility bandwidth are exact zeros. -/
theorem powerLawGegenbauerCoefficients_eq_zero_of_gap {α lam : ℝ} {k n j : ℕ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hzero : lam ≠ 0) (hk : lam+α/2 = k)
    (hgap : n+2*k < j ∨ j+2*k < n) :
    powerLawGegenbauerCoefficients ((PowerLawOperatorData.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩ hzero).atDegree n) k j = 0 := by
  rcases hgap with h | h
  · exact powerLawGegenbauerCoefficients_eq_zero_of_degree ((PowerLawOperatorData.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩ hzero).atDegree n) k j h
  · have hs := integralInner_powerLawGegenbauerOperator_comm hα hlam hzero hk
      (gegenbauer lam n) (gegenbauer lam j)
    dsimp only [integralInner, IntegrablePair.of] at hs
    erw [powerLawGegenbauerOperator_gegenbauer, powerLawGegenbauerOperator_gegenbauer] at hs
    have hz := (isOrthogonal_gegenbauerSequence hlam hzero).integralInner_eq_zero_of_degree_lt
      (hasFiniteMoments_gegenbauerMeasure hlam)
      (degree_le_natDegree.trans_lt (by exact_mod_cast
        (natDegree_powerLawGegenbauerPolynomial_le k j (.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩ j)).trans_lt h))
    change integralInner (gegenbauerMeasure lam) (IntegrablePair.of (gegenbauerMeasure lam) (powerLawGegenbauerPolynomial k j (.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩ j)) (gegenbauer lam n)) = 0 at hz
    unfold powerLawGegenbauerCoefficients gegenbauerBasis
    erw [(isOrthogonal_gegenbauerSequence hlam hzero).basis_repr_eq_integralInner_div
      (hasFiniteMoments_gegenbauerMeasure hlam) (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam)]
    change integralInner (gegenbauerMeasure lam) (IntegrablePair.of (gegenbauerMeasure lam) (powerLawGegenbauerPolynomial k n (.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩ n)) (gegenbauer lam j)) / _ = 0
    dsimp only [integralInner, IntegrablePair.of] at hz ⊢
    erw [hs, hz, zero_div]

/-- In row-output/column-input convention the exact coefficient matrix has
lower and upper bandwidth `2*k`. -/
theorem powerLawGegenbauerCoefficients_isBanded {α lam : ℝ} {k : ℕ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hzero : lam ≠ 0) (hk : lam+α/2 = k) :
    Matrix.IsBanded (fun i j ↦ powerLawGegenbauerCoefficients ((PowerLawOperatorData.ofIntegrable ⟨α,hα⟩ ⟨lam,hlam⟩ hzero).atDegree j) k i) (2*k) (2*k) :=
  fun _ _ h ↦ powerLawGegenbauerCoefficients_eq_zero_of_gap hα hlam hzero hk h

end Real
