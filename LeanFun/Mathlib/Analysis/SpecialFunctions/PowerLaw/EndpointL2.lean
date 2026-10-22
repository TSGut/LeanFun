/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.SingularMass
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.L2Coefficients

/-! # Power-law approximation throughout the strict endpoint-integrable range

The combined endpoint exponent now supplies the uniform mass hypothesis for
closed-interval approximation, the common-space L² operator and normalized
coefficient finite sections. Reference: Gutleb–Carrillo–Olver,
arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped ENNReal InnerProductSpace Topology
namespace Real



end Real
namespace Real

theorem exists_powerLawCoefficientOperator_of_endpointOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (hz : lam.val ≠ 0) (hs : -(1/2) < α.val+lam.val) :
    ∃ p : PowerLawL2Data α.val lam.val, 0 < (p.bound : ℝ) ∧
      ‖powerLawCoefficientOperator p hz‖ ≤ (p.bound : ℝ) ∧
      ∀ c : lp (fun _ : ℕ ↦ ℝ) 2,
        Tendsto (fun N ↦ ∑ i ∈ Finset.range N, lp.single 2 i
          (powerLawCoefficientOperator p hz (∑ j ∈ Finset.range N,lp.single 2 j (c j)) i))
          atTop (𝓝 (powerLawCoefficientOperator p hz c)) := by
  obtain ⟨p,hp⟩ := exists_powerLawL2Data_of_endpoint α lam hs
  exact ⟨p,hp,norm_powerLawCoefficientOperator_leOn p hz,
    tendsto_powerLawCoefficientOperator_finiteSectionsOn p hz⟩
end Real
