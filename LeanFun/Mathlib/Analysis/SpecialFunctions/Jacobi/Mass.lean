/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Measure
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalDensity
import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.BetaDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # The total Jacobi mass
The Beta integral gives the degree-zero squared norm without a removable
singularity at α+β+1=0. Reference: DLMF Table 18.3.1.
-/
public section
open MeasureTheory Set Real
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- The classical Gamma formula; every displayed Gamma value excludes its poles. -/
theorem integral_one_jacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ∫ _ : ℝ, (1 : ℝ) ∂jacobiMeasure α β =
      (2 : ℝ) ^ (α + β + 1) * GammaOn (GammaPoint.ofPos (α + 1) (by linarith)) * GammaOn (GammaPoint.ofPos (β + 1) (by linarith)) / GammaOn (GammaPoint.ofPos (α + β + 2) (by linarith)) := by
  let aa : Complex.BetaParameter := ⟨((β+1 : ℝ) : ℂ), by simpa using (show 0 < β+1 by linarith)⟩
  let bb : Complex.BetaParameter := ⟨((α+1 : ℝ) : ℂ), by simpa using (show 0 < α+1 by linarith)⟩
  have hB : ((∫ t : Ioo (0 : ℝ) 1, (1-(t : ℝ))^α*(t : ℝ)^β : ℝ) : ℂ) =
      Complex.betaIntegralOn aa bb := by
    rw [← integral_complex_ofReal, Complex.betaIntegralOn]
    simp only [Measure.Subtype.volume_def]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [aa,bb]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (by linarith [t.property.2]),
      Complex.ofReal_cpow t.property.1.le]
    have h1 : (((β+1 : ℝ) : ℂ)-1) = (β : ℂ) := by push_cast; ring
    have h2 : (((α+1 : ℝ) : ℂ)-1) = (α : ℂ) := by push_cast; ring
    rw [h1,h2]
    push_cast
    ring
  have hG := Complex.betaIntegralOn_eq_Gamma aa bb
  change Complex.betaIntegralOn aa bb = Complex.Gamma ((β+1 : ℝ) : ℂ) *
    Complex.Gamma ((α+1 : ℝ) : ℂ) /
    Complex.Gamma (((β+1 : ℝ) : ℂ)+((α+1 : ℝ) : ℂ)) at hG
  have hs : (((β+1 : ℝ) : ℂ)+((α+1 : ℝ) : ℂ)) = ((α+β+2 : ℝ) : ℂ) := by push_cast; ring
  rw [hs,Complex.Gamma_ofReal,Complex.Gamma_ofReal,Complex.Gamma_ofReal] at hG
  have hR : (∫ t : Ioo (0 : ℝ) 1, (1-(t : ℝ))^α*(t : ℝ)^β) =
      Real.Gamma (β+1) * Real.Gamma (α+1) / Real.Gamma (α+β+2) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_div,Complex.ofReal_mul] using hB.trans hG
  have hi : Integrable (fun _ : ℝ ↦ (1 : ℝ)) (unitJacobiMeasure α β) := by
    rw [unitJacobiMeasure, integrable_map_measure (by fun_prop) (by fun_prop)]
    exact integrable_jacobiMeasure hα hβ continuousOn_const
  have haff := integral_unitJacobiMeasure α β ⟨fun _ ↦ 1,hi⟩
  have hd := integral_unitJacobiMeasure_subtype α β ⟨fun _ ↦ 1,hi⟩ measurable_const
  simp only at haff hd
  simp only [mul_one] at hd
  rw [← haff,hd]
  simp_rw [unitJacobiWeight_apply]
  rw [integral_const_mul,hR]
  simp only [GammaOn, GammaPoint.ofPos]
  ring

/-- The classical Gamma formula; every displayed Gamma value excludes its poles. -/
theorem integral_jacobiWeight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ∫ x : Ioo (-1 : ℝ) 1, (jacobiWeight α β x : ℝ) =
      (2 : ℝ) ^ (α + β + 1) * GammaOn (GammaPoint.ofPos (α + 1) (by linarith)) * GammaOn (GammaPoint.ofPos (β + 1) (by linarith)) / GammaOn (GammaPoint.ofPos (α + β + 2) (by linarith)) := by
  have h := integral_jacobiMeasure α β
    ⟨fun _ ↦ 1, integrable_jacobiMeasure hα hβ continuousOn_const⟩
  simp only [mul_one] at h
  exact h.symm.trans (integral_one_jacobiMeasure hα hβ)

end Polynomial
