/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerFirstMode
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Differentiation of power-law integrals

Differentiation under the fixed integral, including integrable endpoint-singular
weights. Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

public section
open Set MeasureTheory Filter
open scoped Topology
namespace Real

/-- Differentiating a smooth convolution kernel against an integrable weight. -/
theorem hasDerivAt_intervalIntegral_sub_mul {g f : ℝ → ℝ}
    (hg : Differentiable ℝ g) (hg' : Continuous (deriv g))
    (hf : IntervalIntegrable f volume (-1) 1) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x ↦ ∫ y in (-1 : ℝ)..1, g (x-y)*f y)
      (∫ y in (-1 : ℝ)..1, deriv g (x-y)*f y) x := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hg'.continuousOn
  have hm := hf.aestronglyMeasurable_restrict_uIoc
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (-1 : ℝ) 1) (bound := fun y ↦ M*‖f y‖)
    (isOpen_Ioo.mem_nhds hx) ?_ ?_ ?_ ?_ (hf.norm.const_mul M) ?_).2
  · exact Eventually.of_forall fun z ↦
      ((hg.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul hm
  · exact hf.continuousOn_mul (hg.continuous.comp
      (continuous_const.sub continuous_id)).continuousOn
  · exact ((hg'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul hm
  · apply Eventually.of_forall
    intro y hy z hz
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM (z-y) ⟨by linarith [hy.2, hz.1],
      by linarith [hy.1, hz.2]⟩) (norm_nonneg _)
  · apply Eventually.of_forall
    intro y _ z _
    simpa only [mul_one, Function.comp_def] using
      ((hg (z-y)).hasDerivAt.comp (h := fun z : ℝ ↦ z-y) z
        ((hasDerivAt_id z).sub_const y)).mul_const (f y)



end Real
