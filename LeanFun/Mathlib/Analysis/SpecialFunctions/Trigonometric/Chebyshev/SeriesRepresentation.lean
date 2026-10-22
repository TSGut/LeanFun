/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Series
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Completeness
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Representation by an absolutely summable Chebyshev series

Uniform convergence and weighted L² completeness identify the sum with the
original continuous function. Reference: ATAP, Chapters 4 and 7.
-/

public section

namespace Polynomial.Chebyshev

open Real Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

/-- Continuous functions agreeing almost everywhere for the Chebyshev weight
agree on the entire approximation interval, including its endpoints. -/
theorem eqOn_of_ae_eq_measureT {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[classicalMeasureT] g) : EqOn f g (Icc (-1) 1) := by
  have hz : (∫ x, |f x - g x| ∂classicalMeasureT) = 0 := by
    calc _ = ∫ x, (0 : ℝ) ∂classicalMeasureT := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [h] with x hx
          simp [hx]
         _ = 0 := by simp
  rw [classicalMeasureT_eq, integral_measureT_eq_integral_cos] at hz
  have hc : Continuous (fun θ ↦ |f (cos θ) - g (cos θ)|) := by fun_prop
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae pi_pos.le
    (Filter.Eventually.of_forall fun θ ↦ abs_nonneg (f (cos θ) - g (cos θ)))
    (hc.intervalIntegrable 0 π)).mp hz
  have heq := Measure.eqOn_Ioc_of_ae_eq volume hae hc.continuousOn continuousOn_const
  have hclosed := heq.closure hc continuous_const
  rw [closure_Ioc pi_pos.ne] at hclosed
  intro x hx
  have he := hclosed ⟨arccos_nonneg x, arccos_le_pi x⟩
  simpa only [cos_arccos hx.1 hx.2, Pi.zero_apply, abs_eq_zero, sub_eq_zero] using he

private noncomputable def extendContinuous (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1) 1)) :
    ℝ →ᵇ ℝ :=
  (BoundedContinuousFunction.mkOfCompact ⟨fun x : Icc (-1 : ℝ) 1 ↦ f x, hf.domRestrict⟩).compContinuous
    ⟨projIcc (-1) 1 (by norm_num), continuous_projIcc⟩

private theorem extendContinuous_apply (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1) 1))
    {x : ℝ} (hx : x ∈ Icc (-1) 1) : extendContinuous f hf x = f x := by
  simp [extendContinuous, projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) hx]
  rfl

/-- If the Chebyshev coefficients of a continuous function are absolutely summable,
its Chebyshev series represents it at every point of `[-1,1]` (ATAP, Chapter 4). -/
theorem hasSum_coefficient_mul_eval_T {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (ha : Summable (fun n ↦ |(coefficient (n := n) ⟨f, by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩)|)) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    HasSum (fun n : ℕ ↦ (coefficient (n := n) ⟨f, by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) * (T ℝ n).eval x) (f x) := by
  let F := extendContinuous f hf
  let P (n : ℕ) : ℝ →ᵇ ℝ := extendContinuous (fun x ↦ (T ℝ n).eval x) (by fun_prop)
  let L : (ℝ →ᵇ ℝ) →L[ℝ] Lp ℝ 2 classicalMeasureT := BoundedContinuousFunction.toLp 2 classicalMeasureT ℝ
  have hP (n : ℕ) : ‖P n‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le zero_le_one).2
    intro y
    change ‖(T ℝ n).eval (projIcc (-1) 1 (by norm_num) y : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs]
    exact abs_eval_T_real_le_one _ (abs_le.mpr (projIcc (-1) 1 (by norm_num) y).property)
  have hLP (n : ℕ) : L (P n) = polynomialToL2 (T ℝ n) := by
    apply Lp.ext
    filter_upwards [(P n).coeFn_toLp 2 classicalMeasureT ℝ, coe_polynomialToL2 (T ℝ n),
      ae_mem_Icc_measureT] with y hy hp hyI
    rw [hy, hp]
    exact extendContinuous_apply _ _ hyI
  have hLF : ∀ n, (coefficient (n := n) ⟨(L F), coefficientInput_integrable_L2 (L F) n⟩) = (coefficient (n := n) ⟨f, by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) := by
    intro n
    apply coefficient_congr_ae
    change (fun y ↦ (L F) y) =ᵐ[classicalMeasureT] f
    filter_upwards [F.coeFn_toLp 2 classicalMeasureT ℝ, ae_mem_Icc_measureT] with y hy hyI
    rw [hy]
    exact extendContinuous_apply _ _ hyI
  have hs : Summable (fun n : ℕ ↦ (coefficient (n := n) ⟨f, by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) • P n) := by
    apply ha.of_norm_bounded
    intro n
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hP n)
  let G : ℝ →ᵇ ℝ := ∑' n : ℕ, (coefficient (n := n) ⟨f, by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) • P n
  have hsum : HasSum (fun n : ℕ ↦ (coefficient (n := n) ⟨f, by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) • polynomialToL2 (T ℝ n)) (L G) := by
    simpa only [map_smul, hLP] using L.hasSum hs.hasSum
  have hsumF : HasSum (fun n : ℕ ↦ (coefficient (n := n) ⟨f, by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) • polynomialToL2 (T ℝ n)) (L F) := by
    simpa only [hLF] using hasSum_coefficient_polynomialToL2 (L F)
  have heqL : L G = L F := hsum.unique hsumF
  have heq : EqOn G F (Icc (-1) 1) := by
    apply eqOn_of_ae_eq_measureT G.continuous F.continuous
    filter_upwards [G.coeFn_toLp 2 classicalMeasureT ℝ, F.coeFn_toLp 2 classicalMeasureT ℝ] with y hyG hyF
    exact hyG.symm.trans ((congrArg (fun h : Lp ℝ 2 classicalMeasureT ↦ h y) heqL).trans hyF)
  have hpoint := (BoundedContinuousFunction.evalCLM ℝ x).hasSum hs.hasSum
  have hPx (n : ℕ) : P n x = (T ℝ n).eval x := extendContinuous_apply _ _ hx
  change HasSum (fun n : ℕ ↦ (coefficient (n := n) ⟨f, by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) * P n x) (G x) at hpoint
  have hFx : F x = f x := extendContinuous_apply f hf hx
  simpa only [hPx, heq hx, hFx] using hpoint

end Polynomial.Chebyshev
