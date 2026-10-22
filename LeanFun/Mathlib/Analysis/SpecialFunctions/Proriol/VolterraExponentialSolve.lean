/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraExponentialSeries

/-! # End-to-end first-kind solves for the exponential Volterra kernel

The parameter lam is any real number. The kernel diagonal is identically one.
Reference: Gutleb's thesis, §2.7, and the exponential power series.
-/
@[expose] public noncomputable section
open Polynomial Set Filter ContinuousLinearMap
open scoped Topology
namespace MvPolynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2
local notation "a" => (fun n ↦ Prod.fst (Nat.unpair n))
local notation "b" => (fun n ↦ Prod.snd (Nat.unpair n))

/-- Finite polynomial kernel obtained by truncating the paired exponential series. -/
def volterraExponentialPartial (lam : ℝ) : ℕ → MvPolynomial (Fin 2) ℝ :=
  volterraSeriesPartial a b (volterraExponentialCoefficient lam)

/-- The preconditioned coefficient operator for the exponential convolution kernel. -/
def volterraExponentialOperator (lam : ℝ) : H →L[ℝ] H :=
  volterraSeriesOperator a b (VolterraSeriesOperatorInput.ofWeight a b
    (volterraExponentialCoefficient lam)
    (summable_volterraExponentialWeight lam (norm_nonneg reflectedJacobiOneZeroL2)
      (norm_nonneg shiftedJacobiOneZeroL2)) le_rfl le_rfl)

/-- Explicit coefficient-tail control of the physical exponential-kernel approximation. -/
theorem norm_volterraExponentialPartial_sub_le (lam : ℝ) {R S : ℝ}
    (hR : 1 ≤ R) (hS : 1 ≤ S) (N : ℕ) (z : Fin 2 → ℝ) (hz : z ∈ Real.volterraTriangle) :
    ‖eval z (volterraExponentialPartial lam N)-Real.exp (lam*(z 0-z 1))‖ ≤
      volterraSeriesTail a b ⟨volterraExponentialCoefficient lam,
        summable_volterraExponentialWeight lam (zero_le_one.trans hR) (zero_le_one.trans hS)⟩ N := by
  have h := norm_volterraSeriesPartial_sub_kernel_le a b (volterraExponentialCoefficient lam) hR hS
    (summable_volterraExponentialWeight lam (zero_le_one.trans hR) (zero_le_one.trans hS)) N ⟨z,hz⟩
  have he := volterraSeriesKernel_exponential lam z
  simp only [volterraSeriesKernel, VolterraSeriesKernelInput.ofTriangle,
    VolterraSeriesKernelInput.ofExponential, VolterraSeriesKernelInput.ofWeight] at h he
  simpa only [volterraExponentialPartial, he] using h

private def outerRadius : ℝ := max 1 ‖reflectedJacobiOneZeroL2‖
private def innerRadius : ℝ := max 2 ‖shiftedJacobiOneZeroL2‖
private theorem outer_one : 1 ≤ outerRadius := le_max_left _ _
private theorem inner_one : 1 < innerRadius := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
private theorem outer_norm : ‖reflectedJacobiOneZeroL2‖ ≤ outerRadius := le_max_right _ _
private theorem inner_norm : ‖shiftedJacobiOneZeroL2‖ ≤ innerRadius := le_max_right _ _
private theorem weights (lam : ℝ) : Summable (fun n ↦ volterraSeriesWeight outerRadius innerRadius
    (Nat.unpair n).1 (Nat.unpair n).2 (volterraExponentialCoefficient lam n)) :=
  summable_volterraExponentialWeight lam (zero_le_one.trans outer_one) (zero_le_one.trans inner_one.le)
private theorem diagonal (lam : ℝ) (x : Icc (0 : ℝ) 1) :
    volterraSeriesKernel a b (VolterraSeriesKernelInput.ofTriangle a b
      (volterraExponentialCoefficient lam) outer_one inner_one.le (weights lam)
      ⟨![(x : ℝ),(x : ℝ)], x.property, x.property.1, le_rfl⟩) ≠ 0 := by
  change volterraSeriesKernel a b
    (VolterraSeriesKernelInput.ofExponential lam ![(x : ℝ),(x : ℝ)]) ≠ 0
  rw [volterraSeriesKernel_exponential]
  exact Real.exp_ne_zero _

/-- Every real exponential parameter gives an invertible raw operator and uniformly stable sections. -/
theorem isUnit_and_stable_volterraExponentialOperator (lam : ℝ) :
    IsUnit (volterraExponentialOperator lam) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N in atTop,
      IsUnit (coerciveFiniteSection (lp.initialL2Projection N) (volterraExponentialOperator lam)) ∧
      ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
        (volterraExponentialOperator lam))‖ ≤ B :=
  isUnit_and_stable_volterraSeriesOperator a b (volterraExponentialCoefficient lam)
    outer_one inner_one outer_norm inner_norm (weights lam) (diagonal lam)

/-- Finite polynomial-kernel solves converge for every real lam and convergent raw data. -/
theorem tendsto_volterraExponentialSection_solution (lam : ℝ) (g : H) (gN : ℕ → H)
    (hg : Tendsto gN atTop (𝓝 g)) :
    Tendsto (fun N ↦ Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
      (volterraPreconditionedL2 (volterraExponentialPartial lam N))) (lp.initialL2Projection N (gN N)))
      atTop (𝓝 (Ring.inverse (volterraExponentialOperator lam) g)) :=
  tendsto_volterraSeriesSection_solution a b (volterraExponentialCoefficient lam)
    outer_one inner_one outer_norm inner_norm (weights lam) (diagonal lam) g gN hg

/-- A uniform physical bound for the exponential kernel, for either sign of lam. -/
theorem norm_volterraExponentialKernel_le (lam : ℝ) (z : Fin 2 → ℝ) (hz : z ∈ Real.volterraTriangle) :
    |Real.exp (lam*(z 0-z 1))| ≤ Real.exp |lam| := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h0 : 0 ≤ z 0-z 1 := sub_nonneg.mpr hz.2.2
  have h1 : z 0-z 1 ≤ 1 := by linarith [hz.1.2,hz.2.1]
  calc
    _ ≤ |lam| *(z 0-z 1) := mul_le_mul_of_nonneg_right (le_abs_self lam) h0
    _ ≤ |lam| *1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg lam)
    _ = _ := mul_one _

/-- The exponential coefficient operator represents the actual weighted reflected integral. -/
theorem volterraExponentialOperator_raw_synthesis (lam : ℝ) :
    shiftedJacobiOneZeroSynthesis.comp (volterraRawDiagonal.comp (volterraExponentialOperator lam)) =
      (Real.jacobiVolterraL2Operator
        (show ContinuousOn (fun z : Fin 2 → ℝ ↦ Real.exp (lam*(z 0-z 1))) Real.volterraTriangle by fun_prop)
        (Real.exp_pos |lam|).le (norm_volterraExponentialKernel_le lam)).comp shiftedJacobiOneZeroSynthesis := by
  let e := volterraSeriesTail a b ⟨volterraExponentialCoefficient lam, weights lam⟩
  have he : ∀ n, 0 ≤ e n := volterraSeriesTail_nonneg _ _ _ outer_one inner_one.le (weights lam)
  have herr := norm_volterraExponentialPartial_sub_le lam outer_one inner_one.le
  have bp (n : ℕ) (z : Fin 2 → ℝ) (hz : z ∈ Real.volterraTriangle) :
      |eval z (volterraExponentialPartial lam n)| ≤ Real.exp |lam|+e n := by
    have hh := abs_add_le (eval z (volterraExponentialPartial lam n)-Real.exp (lam*(z 0-z 1)))
      (Real.exp (lam*(z 0-z 1)))
    rw [sub_add_cancel] at hh
    have ht := herr n z hz
    change |eval z (volterraExponentialPartial lam n)-Real.exp (lam*(z 0-z 1))| ≤ e n at ht
    linarith [norm_volterraExponentialKernel_le lam z hz]
  exact Real.jacobiVolterraL2Operator_raw_limit (by fun_prop) (Real.exp_pos |lam|).le
    (norm_volterraExponentialKernel_le lam) (volterraExponentialPartial lam)
    (fun n ↦ add_nonneg (Real.exp_pos |lam|).le (he n)) bp he herr
    (tendsto_volterraSeriesTail _ _ _ (weights lam)) _
    (tendsto_volterraSeriesPartial_operator a b (volterraExponentialCoefficient lam)
      (weights lam) outer_norm inner_norm)

/-- The coefficient solution satisfies the genuine exponential-kernel integral equation. -/
theorem jacobiVolterraL2Operator_exponential_solution (lam : ℝ) (g : H) :
    Real.jacobiVolterraL2Operator
      (show ContinuousOn (fun z : Fin 2 → ℝ ↦ Real.exp (lam*(z 0-z 1))) Real.volterraTriangle by fun_prop)
      (Real.exp_pos |lam|).le (norm_volterraExponentialKernel_le lam)
      (shiftedJacobiOneZeroSynthesis (Ring.inverse (volterraExponentialOperator lam) g)) =
        shiftedJacobiOneZeroSynthesis (volterraRawDiagonal g) := by
  have hb := congrArg (fun T ↦ T (Ring.inverse (volterraExponentialOperator lam) g))
    (volterraExponentialOperator_raw_synthesis lam)
  have hu := (isUnit_and_stable_volterraExponentialOperator lam).1
  have he : volterraExponentialOperator lam (Ring.inverse (volterraExponentialOperator lam) g) = g :=
    congrArg (fun T : H →L[ℝ] H ↦ T g) (Ring.mul_inverse_cancel _ hu)
  simpa only [comp_apply,he] using hb.symm
end MvPolynomial
