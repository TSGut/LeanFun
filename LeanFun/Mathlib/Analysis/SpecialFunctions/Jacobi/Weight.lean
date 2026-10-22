/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Measure
public import LeanFun.Mathlib.Analysis.Calculus.Deriv.OpenDomain
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-! # Calculus of the Jacobi weight
The shifted weight vanishes at both endpoints, even when the original weight
is singular there. Reference: DLMF Tables 18.3.1 and 18.8.1.
-/
public section
open Set Real Filter MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace
open scoped NNReal Topology
namespace Polynomial

/-- Multiplying the weight by `1-x²` shifts both parameters (DLMF Table 18.8.1). -/
private theorem jacobiWeight_add_one_rpow (α β : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    ((1 - (x : ℝ)) ^ ((α + 1)) * (1 + (x : ℝ)) ^ ((β + 1))) = (1 - x ^ 2) * ((1 - (x : ℝ)) ^ (α) * (1 + (x : ℝ)) ^ (β)) := by
  rw [rpow_add (by linarith [hx.2] : 0 < 1 - x),
    rpow_add (by linarith [hx.1] : 0 < 1 + x), rpow_one, rpow_one]
  ring

/-- The shifted weight satisfies the Pearson derivative identity (DLMF Table 18.8.1). -/
private theorem hasDerivAt_jacobiWeight_add_one_rpow (α β : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    HasDerivAt ((fun jacobiPoint : ℝ ↦ ((1 - (jacobiPoint : ℝ)) ^ ((α + 1)) * (1 + (jacobiPoint : ℝ)) ^ ((β + 1)))))
      ((β - α - (α + β + 2) * x) * ((1 - (x : ℝ)) ^ (α) * (1 + (x : ℝ)) ^ (β))) x := by
  have hl := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).rpow_const
    (p := α + 1) (Or.inl (by change 1 - x ≠ 0; linarith [hx.2]))
  have hr := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).rpow_const
    (p := β + 1) (Or.inl (by change 1 + x ≠ 0; linarith [hx.1]))
  convert hl.mul hr using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.add_apply, id_eq, add_sub_cancel_right, zero_sub, zero_add]
    rw [rpow_add (by linarith [hx.2] : 0 < 1 - x),
      rpow_add (by linarith [hx.1] : 0 < 1 + x), rpow_one, rpow_one]
    ring

/-- The classical continuous extension for nonnegative exponents (DLMF 18.3.1). -/
@[expose] noncomputable def jacobiWeightClosed (α β : ℝ≥0) : C(Icc (-1 : ℝ) 1, ℝ≥0) where
  toFun x := ⟨(1 - (x : ℝ)) ^ (α : ℝ) * (1 + (x : ℝ)) ^ (β : ℝ),
    mul_nonneg (Real.rpow_nonneg (by linarith [x.property.2]) _)
      (Real.rpow_nonneg (by linarith [x.property.1]) _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub continuous_subtype_val).rpow_const (fun _ ↦ Or.inr α.property)).mul
      ((continuous_const.add continuous_subtype_val).rpow_const (fun _ ↦ Or.inr β.property))

/-- The closed extension has the power formula, including its regular endpoints. -/
theorem jacobiWeightClosed_apply (α β : ℝ≥0) (x : Icc (-1 : ℝ) 1) :
    (jacobiWeightClosed α β x : ℝ) = (1 - (x : ℝ)) ^ (α : ℝ) *
      (1 + (x : ℝ)) ^ (β : ℝ) := rfl

/-- The closed extension agrees with the original weight on its open domain. -/
theorem jacobiWeightClosed_restrict (α β : ℝ≥0) (x : Ioo (-1 : ℝ) 1) :
    (jacobiWeightClosed α β ⟨x, Ioo_subset_Icc_self x.property⟩ : ℝ) =
      (jacobiWeight α β x : ℝ) := rfl

/-- Multiplying by `1-x²` shifts both parameters on the classical domain. -/
theorem jacobiWeight_add_one (α β : ℝ) (x : Ioo (-1 : ℝ) 1) :
    (jacobiWeight (α + 1) (β + 1) x : ℝ) =
      (1 - (x : ℝ) ^ 2) * (jacobiWeight α β x : ℝ) :=
  jacobiWeight_add_one_rpow α β x.property

/-- The Pearson identity is an actual derivative of the open-domain weight. -/
theorem hasDerivAt_jacobiWeight_add_one (α β : ℝ) (x : Ioo (-1 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (jacobiWeight (α + 1) (β + 1) y : ℝ))
      ((β - α - (α + β + 2) * (x : ℝ)) * (jacobiWeight α β x : ℝ)) x := by
  classical
  -- Extend by zero off the interval; only the germ at the interior point `x`, where both
  -- power bases are positive, enters the derivative.
  refine ⟨fun t ↦ if h : t ∈ Ioo (-1 : ℝ) 1 then (jacobiWeight (α + 1) (β + 1) ⟨t, h⟩ : ℝ)
    else 0, fun y ↦ by simp, ?_⟩
  have hev : (fun t ↦ (1 - t) ^ (α + 1) * (1 + t) ^ (β + 1)) =ᶠ[𝓝 (x : ℝ)]
      fun t ↦ if h : t ∈ Ioo (-1 : ℝ) 1 then (jacobiWeight (α + 1) (β + 1) ⟨t, h⟩ : ℝ)
        else 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds x.property] with t ht
    simp [ht, jacobiWeight_apply]
  exact (hasDerivAt_jacobiWeight_add_one_rpow α β x.property).congr_of_eventuallyEq hev.symm

/-- The right endpoint limit exists with no condition on the opposite exponent. -/
theorem tendsto_jacobiWeight_add_one_one {α β : ℝ} (hα : -1 < α) :
    Tendsto (fun x : Ioo (-1 : ℝ) 1 ↦ (jacobiWeight (α + 1) (β + 1) x : ℝ))
      (Filter.comap Subtype.val (𝓝 (1 : ℝ))) (𝓝 0) := by
  have hval : Tendsto (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ)
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 1) := Filter.tendsto_comap
  -- The vanishing base is a nonnegative real, so its power is taken in `ℝ≥0`.
  let u : Ioo (-1 : ℝ) 1 → ℝ≥0 := fun x ↦ ⟨1 - (x : ℝ), by linarith [x.property.2]⟩
  have hu : Tendsto u (Filter.comap Subtype.val (𝓝 1)) (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hval
    rw [sub_self] at h
    exact h
  have h1 : Tendsto (fun x : Ioo (-1 : ℝ) 1 ↦ (1 - (x : ℝ)) ^ (α + 1))
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 0) := by
    have h := ((NNReal.continuous_rpow_const (by linarith : (0 : ℝ) ≤ α + 1)).tendsto 0).comp hu
    rw [NNReal.zero_rpow (by linarith : α + 1 ≠ 0)] at h
    exact NNReal.tendsto_coe.mpr h
  -- The other base tends to `2`, so it stays positive near the endpoint.
  have h2 : Tendsto (fun x : Ioo (-1 : ℝ) 1 ↦ (1 + (x : ℝ)) ^ (β + 1))
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 ((1 + 1) ^ (β + 1))) :=
    ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))).tendsto.comp hval
  have h := h1.mul h2
  rw [zero_mul] at h
  exact h

/-- The left endpoint limit exists with no condition on the opposite exponent. -/
theorem tendsto_jacobiWeight_add_one_neg_one {α β : ℝ} (hβ : -1 < β) :
    Tendsto (fun x : Ioo (-1 : ℝ) 1 ↦ (jacobiWeight (α + 1) (β + 1) x : ℝ))
      (Filter.comap Subtype.val (𝓝 (-1 : ℝ))) (𝓝 0) := by
  have hval : Tendsto (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ)
      (Filter.comap Subtype.val (𝓝 (-1))) (𝓝 (-1)) := Filter.tendsto_comap
  -- The vanishing base is a nonnegative real, so its power is taken in `ℝ≥0`.
  let v : Ioo (-1 : ℝ) 1 → ℝ≥0 := fun x ↦ ⟨1 + (x : ℝ), by linarith [x.property.1]⟩
  have hv : Tendsto v (Filter.comap Subtype.val (𝓝 (-1))) (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hval
    rw [add_neg_cancel] at h
    exact h
  have h2 : Tendsto (fun x : Ioo (-1 : ℝ) 1 ↦ (1 + (x : ℝ)) ^ (β + 1))
      (Filter.comap Subtype.val (𝓝 (-1))) (𝓝 0) := by
    have h := ((NNReal.continuous_rpow_const (by linarith : (0 : ℝ) ≤ β + 1)).tendsto 0).comp hv
    rw [NNReal.zero_rpow (by linarith : β + 1 ≠ 0)] at h
    exact NNReal.tendsto_coe.mpr h
  -- The other base tends to `2`, so it stays positive near the endpoint.
  have h1 : Tendsto (fun x : Ioo (-1 : ℝ) 1 ↦ (1 - (x : ℝ)) ^ (α + 1))
      (Filter.comap Subtype.val (𝓝 (-1))) (𝓝 ((1 - -1) ^ (α + 1))) :=
    ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num))).tendsto.comp hval
  have h := h1.mul h2
  rw [mul_zero] at h
  exact h

/-- The right endpoint value of the regular continuous extension. -/
theorem jacobiWeightClosed_one (α β : ℝ≥0) :
    (jacobiWeightClosed α β ⟨1, by constructor <;> norm_num⟩ : ℝ) =
      if α = 0 then (2 : ℝ) ^ (β : ℝ) else 0 := by
  by_cases h : α = 0
  · subst α
    norm_num [jacobiWeightClosed_apply]
  · have hr : (α : ℝ) ≠ 0 := by exact_mod_cast h
    simp [jacobiWeightClosed_apply, h, Real.zero_rpow hr]

/-- The left endpoint value of the regular continuous extension. -/
theorem jacobiWeightClosed_neg_one (α β : ℝ≥0) :
    (jacobiWeightClosed α β ⟨-1, by constructor <;> norm_num⟩ : ℝ) =
      if β = 0 then (2 : ℝ) ^ (α : ℝ) else 0 := by
  by_cases h : β = 0
  · subst β
    norm_num [jacobiWeightClosed_apply]
  · have hr : (β : ℝ) ≠ 0 := by exact_mod_cast h
    simp [jacobiWeightClosed_apply, h, Real.zero_rpow hr]

/-- Integration by parts over the classical open weight domain (DLMF 18.8.1). -/
theorem integral_eq_zero_of_hasDerivAt_jacobiWeight_mul {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {f : ℝ → ℝ} {g : Ioo (-1 : ℝ) 1 → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1))
    (hd : ∀ x : Ioo (-1 : ℝ) 1,
      HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
        (fun y ↦ (jacobiWeight (α + 1) (β + 1) y : ℝ) * f y) (g x) x)
    (hg : Integrable g volume) : (∫ x : Ioo (-1 : ℝ) 1, g x) = 0 := by
  classical
  let a : ℝ≥0 := ⟨α + 1, by linarith⟩
  let b : ℝ≥0 := ⟨β + 1, by linarith⟩
  let F : ℝ → ℝ := fun t ↦ if h : t ∈ Icc (-1 : ℝ) 1 then
    (jacobiWeightClosed a b ⟨t, h⟩ : ℝ) * f t else 0
  let G : ℝ → ℝ := fun t ↦ if h : t ∈ Ioo (-1 : ℝ) 1 then g ⟨t, h⟩ else 0
  have hF (x : Ioo (-1 : ℝ) 1) : F x =
      (jacobiWeight (α + 1) (β + 1) x : ℝ) * f x := by
    simp only [F, dite_eq_left (Ioo_subset_Icc_self x.property)]
    rw [jacobiWeightClosed_restrict]
    rfl
  have hG (x : Ioo (-1 : ℝ) 1) : G x = g x := by simp only [G, dite_eq_left x.property]
  have hc : ContinuousOn F (Icc (-1) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (fun x : Icc (-1 : ℝ) 1 ↦ F x) =
        fun x ↦ (jacobiWeightClosed a b x : ℝ) * f x := by
      funext x
      simp only [F, dite_eq_left x.property]
    change Continuous (fun x : Icc (-1 : ℝ) 1 ↦ F x)
    rw [he]
    exact ((NNReal.continuous_coe.comp (jacobiWeightClosed a b).continuous).mul
      (continuousOn_iff_continuous_domRestrict.mp hf))
  have hdF : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (G x) x := by
    intro x hx
    rw [hG ⟨x, hx⟩]
    exact (hasDerivAtOnOpen_iff _ _ _ ⟨x,hx⟩ F hF).mp (hd ⟨x,hx⟩)
  have hiG : IntegrableOn G (Ioo (-1 : ℝ) 1) := by
    rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
    exact hg.congr (Eventually.of_forall fun x ↦ (hG x).symm)
  have hint : IntervalIntegrable G volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).2 hiG
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 : ℝ) ≤ 1) hc hdF hint
  have hright : F 1 = 0 := by
    dsimp only [F]
    rw [dite_eq_left (show (1 : ℝ) ∈ Icc (-1) 1 by constructor <;> norm_num),
      jacobiWeightClosed_apply]
    change ((1 - 1 : ℝ) ^ (α + 1) * (1 + 1 : ℝ) ^ (β + 1)) * f 1 = 0
    simp [Real.zero_rpow (by linarith : α + 1 ≠ 0)]
  have hleft : F (-1) = 0 := by
    dsimp only [F]
    rw [dite_eq_left (show (-1 : ℝ) ∈ Icc (-1) 1 by constructor <;> norm_num),
      jacobiWeightClosed_apply]
    change ((1 - -1 : ℝ) ^ (α + 1) * (1 + -1 : ℝ) ^ (β + 1)) * f (-1) = 0
    simp [Real.zero_rpow (by linarith : β + 1 ≠ 0)]
  rw [hright, hleft, sub_self] at hi
  calc
    (∫ x : Ioo (-1 : ℝ) 1, g x) = ∫ x : Ioo (-1 : ℝ) 1, G x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ (hG x).symm
    _ = ∫ x in Ioo (-1 : ℝ) 1, G x := integral_subtype measurableSet_Ioo G
    _ = ∫ x in (-1 : ℝ)..1, G x := by
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        restrict_Ioo_eq_restrict_Ioc]
    _ = 0 := hi

end Polynomial
