/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.L2Operator
public import LeanFun.Mathlib.Analysis.InnerProductSpace.HilbertBasisOperator

/-! # Convergent power-law coefficient operators

The Gegenbauer Hilbert basis uses orthonormal coefficients in real ℓ².
Finite input and output coordinate truncations converge strongly, without
claiming finite bandwidth or convergence of inverse solves.
Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped ENNReal InnerProductSpace Topology
namespace Real

/-- The bounded power-law operator in normalized Gegenbauer Hilbert coordinates. -/
def powerLawCoefficientOperator {α lam : ℝ} (p : PowerLawL2Data α lam) (hzero : lam ≠ 0) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  (hilbertBasisGegenbauer p.weight_mem hzero).coefficientOperator (powerLawL2Operator p)


end Real
namespace Real

theorem norm_powerLawCoefficientOperator_leOn {α lam : ℝ} (p : PowerLawL2Data α lam)
    (hzero : lam ≠ 0) : ‖powerLawCoefficientOperator p hzero‖ ≤ (p.bound : ℝ) := by
  rw [powerLawCoefficientOperator,(hilbertBasisGegenbauer p.weight_mem hzero).norm_coefficientOperator]
  exact norm_powerLawL2Operator_leOn p

theorem powerLawCoefficientOperator_reprOn {α lam : ℝ} (p : PowerLawL2Data α lam)
    (hzero : lam ≠ 0) (f : Lp ℝ 2 (gegenbauerMeasure lam)) :
    powerLawCoefficientOperator p hzero ((hilbertBasisGegenbauer p.weight_mem hzero).repr f) =
      (hilbertBasisGegenbauer p.weight_mem hzero).repr (powerLawL2Operator p f) := by
  exact (hilbertBasisGegenbauer p.weight_mem hzero).coefficientOperator_repr (powerLawL2Operator p) f

theorem tendsto_powerLawCoefficientOperator_finiteSectionsOn {α lam : ℝ}
    (p : PowerLawL2Data α lam) (hzero : lam ≠ 0) (c : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N ↦ ∑ i ∈ Finset.range N, lp.single 2 i
      (powerLawCoefficientOperator p hzero (∑ j ∈ Finset.range N, lp.single 2 j (c j)) i))
      atTop (𝓝 (powerLawCoefficientOperator p hzero c)) :=
  lp.tendsto_initialL2Sections (powerLawCoefficientOperator p hzero) c
end Real
