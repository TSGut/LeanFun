/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraSeriesRegularity

/-! # First-kind solves from a single coefficient criterion

Absolute coefficient summability supplies both approximation hypotheses and
slice regularity. Only nonvanishing of the diagonal remains a separate kernel
condition. Reference: Gutleb's thesis, §2.7.
-/
@[expose] public noncomputable section
open Polynomial Set Filter ContinuousLinearMap
open scoped Topology
namespace MvPolynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2
variable (i j : ℕ → ℕ) (c : ℕ → ℝ) {R S : ℝ} (hR : 1 ≤ R) (hS : 1 < S)
  (hRH : ‖reflectedJacobiOneZeroL2‖ ≤ R) (hSJ : ‖shiftedJacobiOneZeroL2‖ ≤ S)
  (hw : Summable (fun n ↦ volterraSeriesWeight R S (i n) (j n) (c n)))
  (hd : ∀ x : Icc (0 : ℝ) 1, volterraSeriesKernel i j
    (VolterraSeriesKernelInput.ofTriangle i j c hR hS.le hw
      ⟨![(x : ℝ),(x : ℝ)], x.property, x.property.1, le_rfl⟩) ≠ 0)

private theorem extension_eq_triangle
    (E : VolterraSeriesKernelExtension i j c (zero_le_one.trans hR)
      (zero_le_one.trans hS.le) hw) (z : Real.volterraTriangle) :
    E.val z = volterraSeriesKernel i j
      (VolterraSeriesKernelInput.ofTriangle i j c hR hS.le hw z) := by
  simpa only [VolterraSeriesKernelInput.ofTriangle] using
    E.property ⟨(z : Fin 2 → ℝ), by
      constructor
      · rw [abs_of_nonneg z.property.1.1]
        exact z.property.1.2.trans hR
      · rw [abs_of_nonneg z.property.2.1]
        exact (z.property.2.2.trans z.property.1.2).trans hS.le⟩

include hR hS hRH hSJ hw hd in
/-- The joint coefficient criterion and a nonzero diagonal imply invertibility and stable sections. -/
theorem isUnit_and_stable_volterraSeriesOperator :
    IsUnit (volterraSeriesOperator i j (VolterraSeriesOperatorInput.ofWeight i j c hw hRH hSJ)) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N in atTop,
      IsUnit (coerciveFiniteSection (lp.initialL2Projection N) (volterraSeriesOperator i j (VolterraSeriesOperatorInput.ofWeight i j c hw hRH hSJ))) ∧
      ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
        (volterraSeriesOperator i j (VolterraSeriesOperatorInput.ofWeight i j c hw hRH hSJ)))‖ ≤ B := by
  obtain ⟨E⟩ := nonempty_volterraSeriesKernelExtension i j c
    (zero_le_one.trans hR) (zero_le_one.trans hS.le) hw
  have hdE (x : Icc (0 : ℝ) 1) : E.val ![(x : ℝ),(x : ℝ)] ≠ 0 := by
    rw [extension_eq_triangle i j c hR hS hw E
      ⟨![(x : ℝ),(x : ℝ)], x.property, x.property.1, le_rfl⟩]
    exact hd x
  obtain ⟨C,hC⟩ := exists_volterraSeriesKernel_relative_derivative_bound i j c hR hS hw E hdE
  have herr (N : ℕ) (z : Fin 2 → ℝ) (hz : z ∈ Real.volterraTriangle) :
      ‖eval z (volterraSeriesPartial i j c N) - E.val z‖ ≤
        volterraSeriesTail i j ⟨c,hw⟩ N := by
    rw [extension_eq_triangle i j c hR hS hw E ⟨z,hz⟩]
    exact norm_volterraSeriesPartial_sub_kernel_le i j c hR hS.le hw N ⟨z,hz⟩
  exact Real.isUnit_and_stable_continuousVolterra
    E.val.continuous.continuousOn
    (fun x hx ↦ absolutelyContinuousOnInterval_volterraSeriesKernel i j c hR hS hw E ⟨x,hx⟩)
    (fun x hx ↦ by
      obtain ⟨g⟩ := IntegrableDerivative.nonempty_of_absolutelyContinuous
        (absolutelyContinuousOnInterval_volterraSeriesKernel i j c hR hS hw E ⟨x,hx⟩)
      refine ⟨g, ?_⟩
      filter_upwards [g.hasDerivAt, MeasureTheory.ae_restrict_mem measurableSet_uIcc] with y hy hmem
      rw [← hy.deriv]
      exact hC ⟨x,hx⟩ ⟨y,by simpa only [uIcc_of_le hx.1] using hmem⟩) (fun x hx ↦ hdE ⟨x,hx⟩)
    (volterraSeriesPartial i j c) (volterraSeriesTail_nonneg i j c hR hS.le hw)
    herr
    (tendsto_volterraSeriesTail i j c hw) _ (tendsto_volterraSeriesPartial_operator i j c hw hRH hSJ)

include hR hS hRH hSJ hw hd in
/-- Polynomial series truncation, data approximation and the solve cutoff converge together. -/
theorem tendsto_volterraSeriesSection_solution (g : H) (gN : ℕ → H)
    (hg : Tendsto gN atTop (𝓝 g)) :
    Tendsto (fun N ↦ Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
      (volterraPreconditionedL2 (volterraSeriesPartial i j c N))) (lp.initialL2Projection N (gN N)))
      atTop (𝓝 (Ring.inverse (volterraSeriesOperator i j (VolterraSeriesOperatorInput.ofWeight i j c hw hRH hSJ)) g)) := by
  obtain ⟨E⟩ := nonempty_volterraSeriesKernelExtension i j c
    (zero_le_one.trans hR) (zero_le_one.trans hS.le) hw
  have hdE (x : Icc (0 : ℝ) 1) : E.val ![(x : ℝ),(x : ℝ)] ≠ 0 := by
    rw [extension_eq_triangle i j c hR hS hw E
      ⟨![(x : ℝ),(x : ℝ)], x.property, x.property.1, le_rfl⟩]
    exact hd x
  obtain ⟨C,hC⟩ := exists_volterraSeriesKernel_relative_derivative_bound i j c hR hS hw E hdE
  have herr (N : ℕ) (z : Fin 2 → ℝ) (hz : z ∈ Real.volterraTriangle) :
      ‖eval z (volterraSeriesPartial i j c N) - E.val z‖ ≤
        volterraSeriesTail i j ⟨c,hw⟩ N := by
    rw [extension_eq_triangle i j c hR hS hw E ⟨z,hz⟩]
    exact norm_volterraSeriesPartial_sub_kernel_le i j c hR hS.le hw N ⟨z,hz⟩
  exact Real.tendsto_continuousVolterra_section_solution
    E.val.continuous.continuousOn
    (fun x hx ↦ absolutelyContinuousOnInterval_volterraSeriesKernel i j c hR hS hw E ⟨x,hx⟩)
    (fun x hx ↦ by
      obtain ⟨g⟩ := IntegrableDerivative.nonempty_of_absolutelyContinuous
        (absolutelyContinuousOnInterval_volterraSeriesKernel i j c hR hS hw E ⟨x,hx⟩)
      refine ⟨g, ?_⟩
      filter_upwards [g.hasDerivAt, MeasureTheory.ae_restrict_mem measurableSet_uIcc] with y hy hmem
      rw [← hy.deriv]
      exact hC ⟨x,hx⟩ ⟨y,by simpa only [uIcc_of_le hx.1] using hmem⟩) (fun x hx ↦ hdE ⟨x,hx⟩)
    (volterraSeriesPartial i j c) (volterraSeriesTail_nonneg i j c hR hS.le hw)
    herr
    (tendsto_volterraSeriesTail i j c hw) _ (tendsto_volterraSeriesPartial_operator i j c hw hRH hSJ)
    g gN hg

include hRH hSJ hw in
/-- A finite solve separates solution truncation, data residual and the explicit coefficient tail.
The inverse norm is retained, rather than replaced by an unproved numerical certificate. -/
theorem norm_volterraSeriesSection_error_le (N L : ℕ) (u g : H)
    (hN : IsUnit (coerciveFiniteSection (lp.initialL2Projection N)
      (volterraPreconditionedL2 (volterraSeriesPartial i j c L)))) :
    ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
        (volterraPreconditionedL2 (volterraSeriesPartial i j c L))) (lp.initialL2Projection N g)-u‖ ≤
      ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
        (volterraPreconditionedL2 (volterraSeriesPartial i j c L)))‖ *
        ((1+‖volterraSeriesOperator i j (VolterraSeriesOperatorInput.ofWeight i j c hw hRH hSJ)‖)*‖lp.initialL2Projection N u-u‖ +
          ‖g-volterraSeriesOperator i j (VolterraSeriesOperatorInput.ofWeight i j c hw hRH hSJ) u‖ + volterraSeriesTail i j ⟨c, hw⟩ L*‖u‖) := by
  apply (lp.norm_approximateCoerciveFiniteSection_error_le
    (volterraSeriesOperator i j (VolterraSeriesOperatorInput.ofWeight i j c hw hRH hSJ)) _ N u g hN).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [norm_sub_rev]
  exact norm_volterraSeriesPartial_sub_operator_le i j c hw hRH hSJ L
end MvPolynomial
