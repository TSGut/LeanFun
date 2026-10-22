/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import LeanFun.Mathlib.MeasureTheory.Integral.ClassicalWeight
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Integrals.ClassicalPower
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-! # The Jacobi measure
The weight is integrable for both parameters greater than -1, including
unbounded endpoint singularities. Reference: DLMF Table 18.3.1.
-/
@[expose] public section
open MeasureTheory Set Real
open scoped NNReal ENNReal
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- The Jacobi weight on its open interval, with nonnegative values. -/
noncomputable def jacobiWeight (α β : ℝ) : C(Ioo (-1 : ℝ) 1, ℝ≥0) where
  toFun x := ⟨(1 - (x : ℝ)) ^ α * (1 + (x : ℝ)) ^ β,
    mul_nonneg (Real.rpow_nonneg (by linarith [x.property.2]) _)
      (Real.rpow_nonneg (by linarith [x.property.1]) _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.mul
    · exact (continuous_const.sub continuous_subtype_val).rpow_const
        (fun x ↦ Or.inl (by change 1 - (x : ℝ) ≠ 0; linarith [x.property.2]))
    · exact (continuous_const.add continuous_subtype_val).rpow_const
        (fun x ↦ Or.inl (by change 1 + (x : ℝ) ≠ 0; linarith [x.property.1]))

/-- The classical Jacobi measure: subtype density followed by inclusion. -/
noncomputable def jacobiMeasure (α β : ℝ) : Measure ℝ :=
  openIntervalWeightMeasure (-1) 1 (jacobiWeight α β)

/-- The typed Jacobi density gives an s-finite measure for every parameter pair. -/
instance jacobiMeasure_sfinite (α β : ℝ) : SFinite (jacobiMeasure α β) := by
  let : IsFiniteMeasure (volume : Measure (Ioo (-1 : ℝ) 1)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  unfold jacobiMeasure openIntervalWeightMeasure
  infer_instance

/-- The defining weight formula only has strictly positive power bases. -/
theorem jacobiWeight_apply (α β : ℝ) (x : Ioo (-1 : ℝ) 1) :
    (jacobiWeight α β x : ℝ) = (1 - (x : ℝ)) ^ α * (1 + (x : ℝ)) ^ β := rfl

/-- Characterization of integrability against the classical Jacobi measure. -/
theorem integrable_jacobiMeasure_iff (α β : ℝ) (f : ℝ → ℝ) :
    Integrable f (jacobiMeasure α β) ↔
      Integrable (fun x : Ioo (-1 : ℝ) 1 ↦ (jacobiWeight α β x : ℝ) * f x) volume :=
  integrable_openIntervalWeightMeasure_iff _ _ _ _

/-- Characterization of its integral for a bundled integrable input. -/
theorem integral_jacobiMeasure (α β : ℝ)
    (f : IntegrableInput (jacobiMeasure α β)) :
    ∫ x, f.val x ∂jacobiMeasure α β =
      ∫ x : Ioo (-1 : ℝ) 1, (jacobiWeight α β x : ℝ) * f.val x :=
  integral_openIntervalWeightMeasure _ _ _ _


/-- Positivity in the open interval (DLMF Table 18.3.1). -/
private theorem jacobiWeight_pos_rpow (α β : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    0 < ((1 - (x : ℝ)) ^ (α) * (1 + (x : ℝ)) ^ (β)) :=
  mul_pos (rpow_pos_of_pos (by linarith [hx.2]) _) (rpow_pos_of_pos (by linarith [hx.1]) _)


/-- All classically integrable endpoint singularities are included (DLMF 18.3.1). -/
theorem integrable_jacobiWeight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    Integrable (fun x : Ioo (-1 : ℝ) 1 ↦ (jacobiWeight α β x : ℝ)) volume := by
  let P : ℝ → ℝ → ℝ := fun a t ↦ if 0 < t then t ^ a else 0
  have hp (a : ℝ) (ha : -1 < a) : IntervalIntegrable (P a) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hraw : IntegrableOn (fun x : ℝ ↦ x ^ a) (Ioo (0 : ℝ) 1) := by
      have h := (integrableOn_iff_comap_subtypeVal (f := fun x : ℝ ↦ x ^ a)
        measurableSet_Ioo).mpr (Real.integrable_rpow_openInterval ⟨a, ha⟩ 0 1)
      simpa using h
    apply hraw.congr_fun
    · intro x hx
      simp [P, hx.1]
    · exact measurableSet_Ioo
  have hl : IntervalIntegrable (fun x : ℝ ↦ P β (1 + x)) volume (-1) 0 := by
    simpa using (hp β hβ).comp_add_left 1
  have hr : IntervalIntegrable (fun x : ℝ ↦ P α (1 - x)) volume 0 1 := by
    simpa using ((hp α hα).comp_sub_left 1).symm
  have hi : IntervalIntegrable (fun x : ℝ ↦ P α (1 - x) * P β (1 + x)) volume (-1) 1 := by
    apply IntervalIntegrable.trans (b := 0)
    · have hreg : ContinuousOn (fun x : ℝ ↦ (1 - x) ^ α) (uIcc (-1) 0) := by
        apply continuousOn_of_forall_continuousAt
        intro x hx
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
        exact (continuousAt_const.sub continuousAt_id).rpow_const
          (Or.inl (by change 1 - x ≠ 0; linarith [hx.2]))
      apply (hl.continuousOn_mul hreg).congr
      intro x hx
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
      simp [P, show 0 < 1 - x by linarith [hx.2]]
    · have hreg : ContinuousOn (fun x : ℝ ↦ (1 + x) ^ β) (uIcc 0 1) := by
        apply continuousOn_of_forall_continuousAt
        intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        exact (continuousAt_const.add continuousAt_id).rpow_const
          (Or.inl (by change 1 + x ≠ 0; linarith [hx.1]))
      apply (hr.mul_continuousOn hreg).congr
      intro x hx
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      simp [P, show 0 < 1 + x by linarith [hx.1]]
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
  apply hi.congr
  filter_upwards [] with x
  dsimp [Function.comp_def, P]
  rw [ite_eq_left (show 0 < 1 - (x : ℝ) by linarith [x.property.2]),
    ite_eq_left (show 0 < 1 + (x : ℝ) by linarith [x.property.1])]
  rfl

/-- Continuous functions on the closed interval are Jacobi-integrable
(DLMF Table 18.3.1). -/
theorem integrable_jacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) : Integrable f (jacobiMeasure α β) := by
  rw [integrable_jacobiMeasure_iff]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hc : Continuous (fun x : Ioo (-1 : ℝ) 1 ↦ f x) :=
    continuousOn_iff_continuous_domRestrict.mp (hf.mono Ioo_subset_Icc_self)
  exact (integrable_jacobiWeight hα hβ).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ hC x (Ioo_subset_Icc_self x.property))

/-- Every polynomial square is integrable (DLMF Table 18.3.1). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_jacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    HasFiniteMoments (jacobiMeasure α β) := by
  intro p
  exact integrable_jacobiMeasure hα hβ (p.continuous.pow 2).continuousOn

/-- Finite total mass (DLMF Table 18.3.1). -/
theorem isFiniteMeasure_jacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IsFiniteMeasure (jacobiMeasure α β) :=
  (hasFiniteMoments_jacobiMeasure hα hβ).isFiniteMeasure

/-- The measure is concentrated on the open interval (DLMF Table 18.3.1). -/
theorem ae_mem_Ioo_jacobiMeasure (α β : ℝ) : ∀ᵐ x ∂jacobiMeasure α β, x ∈ Ioo (-1) 1 := by
  -- The measure is pushed forward from the open interval itself.
  rw [jacobiMeasure, openIntervalWeightMeasure]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_Ioo : MeasurableSet {x : ℝ | x ∈ Ioo (-1) 1})).2
    (Filter.Eventually.of_forall fun x ↦ x.property)

/-- Strict positivity at every point of the classical domain (DLMF Table 18.3.1). -/
theorem jacobiWeight_pos (α β : ℝ) (x : Ioo (-1 : ℝ) 1) :
    0 < (jacobiWeight α β x : ℝ) :=
  jacobiWeight_pos_rpow α β x.property

/-- Strict positivity of the polynomial pairing (DLMF 18.2(i), Table 18.3.1). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_jacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    HasPositiveDefiniteIntegral (jacobiMeasure α β) := by
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  have hex : ∃ x ∈ Ioo (-1 : ℝ) 1, p.eval x ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (p.eq_zero_of_infinite_isRoot
      ((Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).mono h))
  have hi := integrable_jacobiMeasure hα hβ (p.continuous.pow 2).continuousOn
  rw [integral_jacobiMeasure α β ⟨fun x ↦ p.eval x ^ 2, hi⟩]
  have hi' := (integrable_jacobiMeasure_iff _ _ _).mp hi
  apply (integral_pos_iff_support_of_nonneg (fun x ↦
    mul_nonneg (jacobiWeight α β x).property (sq_nonneg _)) hi').2
  let : (volume : Measure (Ioo (-1 : ℝ) 1)).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume isOpen_Ioo.isOpenEmbedding_subtypeVal
  have ho : IsOpen {x : Ioo (-1 : ℝ) 1 | p.eval (x : ℝ) ≠ 0} :=
    isOpen_ne.preimage (p.continuous.comp continuous_subtype_val)
  have hn : ({x : Ioo (-1 : ℝ) 1 | p.eval (x : ℝ) ≠ 0} : Set _).Nonempty := by
    obtain ⟨x, hx, hp⟩ := hex
    exact ⟨⟨x, hx⟩, hp⟩
  apply (ho.measure_pos volume hn).trans_le
  apply measure_mono
  intro x hx
  exact mul_ne_zero (jacobiWeight_pos α β x).ne' (pow_ne_zero _ hx)

/-- The domain-typed Jacobi weight is measurable (DLMF Table 18.3.1). -/
theorem measurable_jacobiWeight (α β : ℝ) : Measurable (jacobiWeight α β) :=
  (jacobiWeight α β).continuous.measurable

/-- Nonnegativity is part of the codomain, without any endpoint evaluation. -/
theorem jacobiWeight_nonneg (α β : ℝ) (x : Ioo (-1 : ℝ) 1) :
    0 ≤ (jacobiWeight α β x : ℝ) := (jacobiWeight α β x).property


end Polynomial
