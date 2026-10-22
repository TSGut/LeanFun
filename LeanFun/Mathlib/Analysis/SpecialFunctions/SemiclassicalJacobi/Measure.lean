/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Existence
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Integrals.ClassicalPower
public import LeanFun.Mathlib.MeasureTheory.Integral.ClassicalWeight
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-! # Semiclassical Jacobi measures
The weight on `(0,1)` is `x^a (1-x)^b (t-x)^c`, with `t > 1`,
`a,b > -1`, and arbitrary real `c`. These are the parameters used in
Papadopoulos–Gutleb–Slevinsky–Olver, *Building hierarchies of semiclassical
Jacobi polynomials for spectral methods in annuli*, Section 3.
-/
@[expose] public section
open MeasureTheory Set Real
open scoped NNReal ENNReal
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- All three power bases are positive on the typed domain. -/
noncomputable def semiclassicalJacobiWeight (t : Ioi (1 : ℝ)) (α β γ : ℝ) : C(Ioo (0 : ℝ) 1, ℝ≥0) where
  toFun x := ⟨(x : ℝ) ^ α * (1 - (x : ℝ)) ^ β * ((t : ℝ) - x) ^ γ,
    mul_nonneg (mul_nonneg (Real.rpow_nonneg x.property.1.le _)
      (Real.rpow_nonneg (by linarith [x.property.2]) _))
      (Real.rpow_nonneg (by have ht : 1 < (t : ℝ) := t.property; linarith [x.property.2]) _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.mul
    · apply Continuous.mul
      · exact continuous_subtype_val.rpow_const (fun x ↦ Or.inl x.property.1.ne')
      · exact (continuous_const.sub continuous_subtype_val).rpow_const
          (fun x ↦ Or.inl (by change 1 - (x : ℝ) ≠ 0; linarith [x.property.2]))
    · exact (continuous_const.sub continuous_subtype_val).rpow_const
        (fun x ↦ Or.inl (by change (t : ℝ) - (x : ℝ) ≠ 0; have ht : 1 < (t : ℝ) := t.property; linarith [x.property.2]))

/-- Subtype density and inclusion define the measure, without endpoint values. -/
noncomputable def semiclassicalJacobiMeasure (t : Ioi (1 : ℝ)) (α β γ : ℝ) : Measure ℝ :=
  openIntervalWeightMeasure 0 1 (semiclassicalJacobiWeight t α β γ)

/-- Characterization of the density on its classical domain. -/
theorem semiclassicalJacobiWeight_apply (t : Ioi (1 : ℝ)) (α β γ : ℝ)
    (x : Ioo (0 : ℝ) 1) :
    (semiclassicalJacobiWeight t α β γ x : ℝ) =
      (x : ℝ) ^ α * (1 - (x : ℝ)) ^ β * ((t : ℝ) - x) ^ γ := rfl

/-- Characterization of integrability, including every convergent endpoint singularity. -/
theorem integrable_semiclassicalJacobiMeasure_iff (t : Ioi (1 : ℝ)) (α β γ : ℝ)
    (f : ℝ → ℝ) :
    Integrable f (semiclassicalJacobiMeasure t α β γ) ↔
      Integrable (fun x : Ioo (0 : ℝ) 1 ↦
        (semiclassicalJacobiWeight t α β γ x : ℝ) * f x) volume :=
  integrable_openIntervalWeightMeasure_iff _ _ _ _

/-- The weighted integral formula for bundled integrable inputs. -/
theorem integral_semiclassicalJacobiMeasure (t : Ioi (1 : ℝ)) (α β γ : ℝ)
    (f : IntegrableInput (semiclassicalJacobiMeasure t α β γ)) :
    ∫ x, f.val x ∂semiclassicalJacobiMeasure t α β γ =
      ∫ x : Ioo (0 : ℝ) 1, (semiclassicalJacobiWeight t α β γ x : ℝ) * f.val x :=
  integral_openIntervalWeightMeasure _ _ _ _



/-- With zero third exponent, the measure is independent of its external point. -/
@[simp] theorem semiclassicalJacobiMeasure_zero_third (t : Ioi (1 : ℝ)) (α β : ℝ) :
    semiclassicalJacobiMeasure t α β 0 =
      semiclassicalJacobiMeasure ⟨2, by norm_num⟩ α β 0 := by
  unfold semiclassicalJacobiMeasure
  congr 1
  ext x
  simp only [semiclassicalJacobiWeight_apply, Real.rpow_zero, mul_one]

/-- Positivity on the open interval for arbitrary real exponents. -/
private theorem semiclassicalJacobiWeight_pos_rpow (t α β γ : ℝ) (ht : 1 < t)
    {x : ℝ} (hx : x ∈ Ioo 0 1) : 0 < ((x : ℝ) ^ (α) * (1 - (x : ℝ)) ^ (β) * ((t : ℝ) - (x : ℝ)) ^ (γ)) :=
  mul_pos (mul_pos (rpow_pos_of_pos hx.1 _)
    (rpow_pos_of_pos (by linarith [hx.2]) _))
    (rpow_pos_of_pos (by linarith [hx.2]) _)

/-- The third factor is continuous on the closed interval, even for negative exponents. -/
theorem continuousOn_semiclassicalJacobi_factor {t : ℝ} (ht : 1 < t) (γ : ℝ) :
    ContinuousOn (fun x : ℝ => (t - x) ^ γ) (Icc 0 1) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  exact (continuousAt_const.sub continuousAt_id).rpow_const
    (Or.inl (by change t - x ≠ 0; linarith [hx.2]))

/-- Continuous functions on the closed interval are integrable for the semiclassical Jacobi measure
(Papadopoulos–Gutleb–Slevinsky–Olver, Section 3). -/
theorem integrable_semiclassicalJacobiMeasure {t α β γ : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Integrable f (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ) := by
  let P : ℝ → ℝ → ℝ := fun a x ↦ if 0 < x then x ^ a else 0
  have hp (a : ℝ) (ha : -1 < a) : IntervalIntegrable (P a) volume 0 (1/2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1/2)]
    have hr : IntegrableOn (fun x : ℝ ↦ x^a) (Ioo (0 : ℝ) (1/2)) := by
      have h := (integrableOn_iff_comap_subtypeVal (f := fun x : ℝ ↦ x^a)
        measurableSet_Ioo).mpr (Real.integrable_rpow_openInterval ⟨a, ha⟩ 0 (1/2))
      simpa using h
    apply hr.congr_fun
    · intro x hx
      simp [P, hx.1]
    · exact measurableSet_Ioo
  have hab : IntervalIntegrable (fun x : ℝ ↦ P α x * P β (1-x)) volume 0 1 := by
    apply IntervalIntegrable.trans (b := 1/2)
    · have hreg : ContinuousOn (fun x : ℝ ↦ (1-x)^β) (uIcc 0 (1/2)) := by
        apply continuousOn_of_forall_continuousAt
        intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at hx
        exact (continuousAt_const.sub continuousAt_id).rpow_const
          (Or.inl (by change 1-x ≠ 0; linarith [hx.2]))
      apply ((hp α hα).mul_continuousOn hreg).congr
      intro x hx
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at hx
      simp [P, show 0 < 1-x by linarith [hx.2]]
    · have hr : IntervalIntegrable (fun x : ℝ ↦ P β (1-x)) volume (1/2) 1 := by
        convert ((hp β hβ).comp_sub_left 1).symm using 1 <;> norm_num
      have hreg : ContinuousOn (fun x : ℝ ↦ x^α) (uIcc (1/2) 1) := by
        apply continuousOn_of_forall_continuousAt
        intro x hx
        rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at hx
        exact continuousAt_id.rpow_const (Or.inl (by change x ≠ 0; linarith [hx.1]))
      apply (hr.continuousOn_mul hreg).congr
      intro x hx
      rw [uIoc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at hx
      simp [P, show 0 < x by linarith [hx.1]]
  have hi := (hab.mul_continuousOn (by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      continuousOn_semiclassicalJacobi_factor ht γ)).mul_continuousOn (by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hf)
  rw [integrable_semiclassicalJacobiMeasure_iff]
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
  apply hi.congr
  filter_upwards [] with x
  simp only [Function.comp_apply, semiclassicalJacobiWeight_apply, P,
    ite_eq_left x.property.1, ite_eq_left (show 0 < 1-(x : ℝ) by linarith [x.property.2])]

/-- Every polynomial square is integrable
(Papadopoulos–Gutleb–Slevinsky–Olver, Section 3). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_semiclassicalJacobiMeasure {t α β γ : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) :
    HasFiniteMoments (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ) := by
  intro p
  exact integrable_semiclassicalJacobiMeasure ht hα hβ (p.continuous.pow 2).continuousOn

/-- Finite total mass
(Papadopoulos–Gutleb–Slevinsky–Olver, Section 3). -/
theorem isFiniteMeasure_semiclassicalJacobiMeasure {t α β γ : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) :
    IsFiniteMeasure (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ) :=
  (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ).isFiniteMeasure

/-- The measure is concentrated on the open interval
(Papadopoulos–Gutleb–Slevinsky–Olver, Section 3). -/
theorem ae_mem_Ioo_semiclassicalJacobiMeasure (t : Ioi (1 : ℝ)) (α β γ : ℝ) :
    ∀ᵐ x ∂semiclassicalJacobiMeasure t α β γ, x ∈ Ioo 0 1 := by
  rw [semiclassicalJacobiMeasure, openIntervalWeightMeasure]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_Ioo : MeasurableSet {x : ℝ | x ∈ Ioo (0 : ℝ) 1})).2
    (Filter.Eventually.of_forall fun x ↦ x.property)

/-- Strict positivity of the polynomial pairing
(Papadopoulos–Gutleb–Slevinsky–Olver, Section 3). -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure {t α β γ : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) :
    HasPositiveDefiniteIntegral (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ) := by
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  have hex : ∃ x ∈ Ioo (0 : ℝ) 1, p.eval x ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (p.eq_zero_of_infinite_isRoot
      ((Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).mono h))
  have hi := integrable_semiclassicalJacobiMeasure (γ := γ) ht hα hβ
    (p.continuous.pow 2).continuousOn
  erw [integral_semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ ⟨_, hi⟩]
  have hi' := (integrable_semiclassicalJacobiMeasure_iff _ _ _ _ _).mp hi
  apply (integral_pos_iff_support_of_nonneg (fun x ↦
    mul_nonneg (semiclassicalJacobiWeight ⟨t, ht⟩ α β γ x).property (sq_nonneg _)) hi').2
  let : (volume : Measure (Ioo (0 : ℝ) 1)).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume isOpen_Ioo.isOpenEmbedding_subtypeVal
  have ho : IsOpen {x : Ioo (0 : ℝ) 1 | p.eval (x : ℝ) ≠ 0} :=
    isOpen_ne.preimage (p.continuous.comp continuous_subtype_val)
  have hn : ({x : Ioo (0 : ℝ) 1 | p.eval (x : ℝ) ≠ 0} : Set _).Nonempty := by
    obtain ⟨x, hx, hp⟩ := hex
    exact ⟨⟨x, hx⟩, hp⟩
  apply (ho.measure_pos volume hn).trans_le
  apply measure_mono
  intro x hx
  exact mul_ne_zero (semiclassicalJacobiWeight_pos_rpow t α β γ ht x.property).ne'
    (pow_ne_zero _ hx)

/-- The admissible semiclassical Jacobi measures admit orthogonal polynomial
sequences of exact degrees. Normalization is not fixed by this existence theorem. -/
theorem exists_isOrthogonal_semiclassicalJacobiMeasure {t α β γ : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) :
    ∃ P : Sequence ℝ, P.IsOrthogonal (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ) :=
  exists_isOrthogonal _ (hasFiniteMoments_semiclassicalJacobiMeasure ht hα hβ)
    (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα hβ)

end Polynomial
