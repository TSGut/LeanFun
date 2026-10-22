/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.CriticalL2

/-! # Critical power-law operators in normalized Gegenbauer coordinates

The weighted Schur construction transports to ℓ² with its norm unchanged.
Finite input and output sections converge strongly, including on the critical
parameter line. Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2,
and the Hilbert-space orthonormal expansion theorem (DLMF 18.2(viii)).
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Filter
open scoped ENNReal InnerProductSpace Topology
namespace Real

/-- The critical power-law operator in normalized Gegenbauer Hilbert coordinates. -/
def criticalPowerLawCoefficientOperator {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hzero : lam ≠ 0) (hcrit : α+lam = -(1/2)) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  (hilbertBasisGegenbauer hlam hzero).coefficientOperator
    (criticalPowerLawL2Operator hα hlam hcrit)

/-- The critical coefficient operator has the same norm as its L² realization. -/
theorem norm_criticalPowerLawCoefficientOperator {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hzero : lam ≠ 0) (hcrit : α+lam = -(1/2)) :
    ‖criticalPowerLawCoefficientOperator hα hlam hzero hcrit‖ =
      ‖criticalPowerLawL2Operator hα hlam hcrit‖ :=
  (hilbertBasisGegenbauer hlam hzero).norm_coefficientOperator _

/-- The explicit critical Schur bound is preserved in normalized coefficient space. -/
theorem norm_criticalPowerLawCoefficientOperator_le {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hzero : lam ≠ 0) (hcrit : α+lam = -(1/2)) :
    ‖criticalPowerLawCoefficientOperator hα hlam hzero hcrit‖ ≤ powerLawSchurConstant (.ofCritical ⟨α,hα,by linarith⟩) := by
  rw [norm_criticalPowerLawCoefficientOperator]
  exact norm_criticalPowerLawL2Operator_leOn hα hlam hcrit

/-- Critical coefficient transport exactly represents the underlying L² action. -/
theorem criticalPowerLawCoefficientOperator_repr {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hzero : lam ≠ 0) (hcrit : α+lam = -(1/2))
    (f : Lp ℝ 2 (gegenbauerMeasure lam)) :
    criticalPowerLawCoefficientOperator hα hlam hzero hcrit
        ((hilbertBasisGegenbauer hlam hzero).repr f) =
      (hilbertBasisGegenbauer hlam hzero).repr (criticalPowerLawL2Operator hα hlam hcrit f) :=
  (hilbertBasisGegenbauer hlam hzero).coefficientOperator_repr _ f


/-- The leading finite critical coefficient sections converge strongly on every ℓ² vector. -/
theorem tendsto_criticalPowerLawCoefficientOperator_finiteSections {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hzero : lam ≠ 0) (hcrit : α+lam = -(1/2))
    (c : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N ↦ ∑ i ∈ Finset.range N, lp.single 2 i
      (criticalPowerLawCoefficientOperator hα hlam hzero hcrit
        (∑ j ∈ Finset.range N, lp.single 2 j (c j)) i))
      atTop (𝓝 (criticalPowerLawCoefficientOperator hα hlam hzero hcrit c)) :=
  lp.tendsto_initialL2Sections (criticalPowerLawCoefficientOperator hα hlam hzero hcrit) c

/-- Applying the critical operator to classical Gegenbauer partial sums converges in L². -/
theorem tendsto_criticalPowerLawL2Operator_gegenbauer_sums {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hzero : lam ≠ 0) (hcrit : α+lam = -(1/2))
    (f : Lp ℝ 2 (gegenbauerMeasure lam)) :
    Tendsto (fun N : ℕ ↦ criticalPowerLawL2Operator hα hlam hcrit
      (∑ n ∈ Finset.range N, (gegenbauerCoefficient lam (IntegralCoefficientInput.ofGegenbauerL2 hlam hzero f n)) •
        polynomialToL2 (hasFiniteMoments_gegenbauerMeasure hlam) (gegenbauer lam n)))
      atTop (𝓝 (criticalPowerLawL2Operator hα hlam hcrit f)) :=
  (criticalPowerLawL2Operator hα hlam hcrit).continuous.tendsto _ |>.comp
    (tendsto_sum_gegenbauerCoefficient_polynomialToL2 hlam hzero f)

end Real
namespace Real

theorem criticalPowerLawCoefficientOperator_singleOn {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (hz : lam ≠ 0) (hc : α+lam = -(1/2)) (i j : ℕ) :
    criticalPowerLawCoefficientOperator hα hlam hz hc (lp.single 2 j 1) i =
      ∫ z : ℝ × ℝ, (hilbertBasisGegenbauer hlam hz i z.1 * hilbertBasisGegenbauer hlam hz j z.2)
        ∂powerLawKernelMeasure α lam := by
  rw [criticalPowerLawCoefficientOperator,HilbertBasis.coefficientOperator_single]
  exact (criticalPowerLawL2Operator_spec hα hlam hc _ _).2
end Real
