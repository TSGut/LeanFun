/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.EndpointTesting
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.CriticalCoefficients
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.ClassicalMeasures
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Completeness

/-! # Power-law coefficients throughout the boundedness range

At parameter zero, use the normalized Chebyshev T basis; elsewhere retain the
normalized Gegenbauer basis. The weak kernel uniquely determines the bounded
operator, so the full-range realization agrees with the earlier constructions.
References: DLMF Table 18.3.1; Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Filter
open scoped ENNReal InnerProductSpace Topology

namespace Polynomial

/-- The zero-parameter Gegenbauer measure is precisely the Chebyshev T measure. -/
theorem gegenbauerMeasure_zero : gegenbauerMeasure 0 = Chebyshev.classicalMeasureT := by
  rw [gegenbauerMeasure_eq_jacobiMeasure, measureT_eq_jacobiMeasure]
  norm_num

/-- The existing normalized Chebyshev basis, transported along equality of measures. -/
def hilbertBasisChebyshevGegenbauerZero : HilbertBasis ℕ ℝ (Lp ℝ 2 (gegenbauerMeasure 0)) :=
  gegenbauerMeasure_zero ▸ Chebyshev.hilbertBasisT

/-- A Hilbert basis for every admissible Gegenbauer measure, including parameter zero. -/
def powerLawHilbertBasis {lam : ℝ} (hlam : -(1/2) < lam) :
    HilbertBasis ℕ ℝ (Lp ℝ 2 (gegenbauerMeasure lam)) :=
  if hz : lam = 0 then hz ▸ hilbertBasisChebyshevGegenbauerZero
  else hilbertBasisGegenbauer hlam hz

/-- At zero the selected basis is normalized Chebyshev T. -/
@[simp] theorem powerLawHilbertBasis_zero (h : -(1/2 : ℝ) < 0) :
    powerLawHilbertBasis h = hilbertBasisChebyshevGegenbauerZero := by
  simp [powerLawHilbertBasis]

/-- Away from zero the established Gegenbauer normalization is preserved. -/
theorem powerLawHilbertBasis_of_ne_zero {lam : ℝ} (hlam : -(1/2) < lam) (hz : lam ≠ 0) :
    powerLawHilbertBasis hlam = hilbertBasisGegenbauer hlam hz := by
  simp [powerLawHilbertBasis, hz]

end Polynomial

namespace Real

/-- The unique weak kernel realization throughout the exact same-space boundedness range. -/
def boundedPowerLawL2Operator {α lam : ℝ} (hα : -1 < α) (hlam : -(1/2) < lam)
    (hs : -(1/2) ≤ α+lam) :
    Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam) :=
  Classical.choose ((exists_powerLawL2Operator_iffOn ⟨α,hα⟩ ⟨lam,hlam⟩).mpr hs)





theorem boundedPowerLawL2Operator_spec {α lam : ℝ} (hα : -1 < α)
    (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam) (f g : Lp ℝ 2 (gegenbauerMeasure lam)) :
    Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α lam) ∧
    ⟪g,boundedPowerLawL2Operator hα hlam hs f⟫_ℝ =
      ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam := by
  have h := Classical.choose_spec ((exists_powerLawL2Operator_iffOn ⟨α,hα⟩ ⟨lam,hlam⟩).mpr hs)
  exact ⟨h.1 f g,h.2 f g⟩

/-- On the critical line the full-range operator is the weighted Schur construction. -/
theorem boundedPowerLawL2Operator_eq_critical {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hc : α+lam = -(1/2)) :
    boundedPowerLawL2Operator hα hlam hc.ge = criticalPowerLawL2Operator hα hlam hc := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [(boundedPowerLawL2Operator_spec hα hlam hc.ge f g).2,(criticalPowerLawL2Operator_spec hα hlam hc f g).2]

/-- Normalized coefficient realization, using Chebyshev T at parameter zero. -/
def boundedPowerLawCoefficientOperator {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  (powerLawHilbertBasis hlam).coefficientOperator (boundedPowerLawL2Operator hα hlam hs)

/-- Coordinate transport preserves the full-range operator norm exactly. -/
theorem norm_boundedPowerLawCoefficientOperator {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam) :
    ‖boundedPowerLawCoefficientOperator hα hlam hs‖ = ‖boundedPowerLawL2Operator hα hlam hs‖ :=
  (powerLawHilbertBasis hlam).norm_coefficientOperator _

/-- The critical norm bound includes the Chebyshev case alpha = -1/2, lambda = 0. -/
theorem norm_boundedPowerLawCoefficientOperator_le_critical {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hc : α+lam = -(1/2)) :
    ‖boundedPowerLawCoefficientOperator hα hlam hc.ge‖ ≤ powerLawSchurConstant (.ofCritical ⟨α,hα,by linarith⟩) := by
  rw [norm_boundedPowerLawCoefficientOperator, boundedPowerLawL2Operator_eq_critical]
  exact norm_criticalPowerLawL2Operator_leOn hα hlam hc

/-- Full-range coefficient action exactly intertwines the L² operator. -/
theorem boundedPowerLawCoefficientOperator_repr {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam)
    (f : Lp ℝ 2 (gegenbauerMeasure lam)) :
    boundedPowerLawCoefficientOperator hα hlam hs ((powerLawHilbertBasis hlam).repr f) =
      (powerLawHilbertBasis hlam).repr (boundedPowerLawL2Operator hα hlam hs f) :=
  (powerLawHilbertBasis hlam).coefficientOperator_repr _ f


/-- Finite coefficient sections converge strongly throughout the exact boundedness range. -/
theorem tendsto_boundedPowerLawCoefficientOperator_finiteSections {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam)
    (c : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N ↦ lp.initialL2Projection N
      (boundedPowerLawCoefficientOperator hα hlam hs (lp.initialL2Projection N c)))
      atTop (𝓝 (boundedPowerLawCoefficientOperator hα hlam hs c)) := by
  simpa only [lp.initialL2Projection_apply] using
    lp.tendsto_initialL2Sections (boundedPowerLawCoefficientOperator hα hlam hs) c


/-- Away from zero, the critical coefficient construction is unchanged. -/
theorem boundedPowerLawCoefficientOperator_eq_critical {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hc : α+lam = -(1/2)) (hz : lam ≠ 0) :
    boundedPowerLawCoefficientOperator hα hlam hc.ge =
      criticalPowerLawCoefficientOperator hα hlam hz hc := by
  simp only [boundedPowerLawCoefficientOperator, criticalPowerLawCoefficientOperator,
    powerLawHilbertBasis_of_ne_zero hlam hz, boundedPowerLawL2Operator_eq_critical hα hlam hc]


end Real

namespace Real

theorem boundedPowerLawL2Operator_eqOn {α lam : ℝ} (hα : -1 < α)
    (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam)
    (T : Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam))
    (he : ∀ f g : Lp ℝ 2 (gegenbauerMeasure lam),
      ⟪g,T f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam) :
    boundedPowerLawL2Operator hα hlam hs = T := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  rw [(boundedPowerLawL2Operator_spec hα hlam hs f g).2,he]
end Real
namespace Real

theorem boundedPowerLawCoefficientOperator_singleOn {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hs : -(1/2) ≤ α+lam) (i j : ℕ) :
    boundedPowerLawCoefficientOperator hα hlam hs (lp.single 2 j 1) i =
      ∫ z : ℝ × ℝ, (powerLawHilbertBasis hlam i z.1 * powerLawHilbertBasis hlam j z.2)
        ∂powerLawKernelMeasure α lam := by
  rw [boundedPowerLawCoefficientOperator,HilbertBasis.coefficientOperator_single]
  exact (boundedPowerLawL2Operator_spec hα hlam hs _ _).2
end Real
namespace Real

theorem boundedPowerLawL2Operator_eq_massOn {α lam : ℝ} (p : PowerLawL2Data α lam)
    (hs : -(1/2) ≤ α+lam) :
    boundedPowerLawL2Operator p.exponent_mem p.weight_mem hs = powerLawL2Operator p :=
  boundedPowerLawL2Operator_eqOn p.exponent_mem p.weight_mem hs _
    (fun f g ↦ (powerLawL2Operator_spec p f g).2)

theorem boundedPowerLawCoefficientOperator_eq_massOn {α lam : ℝ} (p : PowerLawL2Data α lam)
    (hs : -(1/2) ≤ α+lam) (hz : lam ≠ 0) :
    boundedPowerLawCoefficientOperator p.exponent_mem p.weight_mem hs =
      powerLawCoefficientOperator p hz := by
  simp only [boundedPowerLawCoefficientOperator,powerLawCoefficientOperator,
    powerLawHilbertBasis_of_ne_zero p.weight_mem hz,boundedPowerLawL2Operator_eq_massOn p hs]

theorem norm_boundedPowerLawCoefficientOperator_le_massOn {α lam : ℝ}
    (p : PowerLawL2Data α lam) (hs : -(1/2) ≤ α+lam) :
    ‖boundedPowerLawCoefficientOperator p.exponent_mem p.weight_mem hs‖ ≤ (p.bound : ℝ) := by
  rw [norm_boundedPowerLawCoefficientOperator,boundedPowerLawL2Operator_eq_massOn p hs]
  exact norm_powerLawL2Operator_leOn p
end Real
