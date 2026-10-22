/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Measure
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial

/-! # Classical symmetric deformation of disk factor measures
The positive branch has its nonnegative radicand domain in the type.
Reference: Dunkl–Xu, §2.6.1 and Chapter 3.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace Polynomial

/-- The positive deformation branch on its entire classical real domain. -/
noncomputable def diskDeformation (δ : ℝ) (x : {x : ℝ // 0 ≤ 1-δ+δ*x^2}) : ℝ :=
  Real.sqrt (1-δ+δ*(x : ℝ)^2)

/-- The branch is continuous on its classical domain. -/
theorem continuous_diskDeformation (δ : ℝ) : Continuous (diskDeformation δ) := by
  unfold diskDeformation
  fun_prop

/-- Squaring recovers the affine squared coordinate everywhere in the domain. -/
theorem diskDeformation_sq (δ : ℝ) (x : {x : ℝ // 0 ≤ 1-δ+δ*x^2}) :
    diskDeformation δ x ^ 2 = 1-δ+δ*(x : ℝ)^2 := Real.sq_sqrt x.property

/-- Parameters in the closed unit interval admit every real source coordinate. -/
theorem diskDeformation_radical_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : ℝ) :
    0 ≤ 1-δ+δ*x^2 := add_nonneg (sub_nonneg.mpr hδ1) (mul_nonneg hδ (sq_nonneg x))

/-- The branch maps unit-interval source points into the unit interval. -/
theorem diskDeformation_mem_Icc {δ : ℝ} (hδ : 0 ≤ δ) (_hδ1 : δ ≤ 1)
    (x : {x : ℝ // 0 ≤ 1-δ+δ*x^2}) (hx : (x : ℝ) ∈ Icc (-1 : ℝ) 1) :
    diskDeformation δ x ∈ Icc (-1 : ℝ) 1 := by
  have hn : 0 ≤ diskDeformation δ x := Real.sqrt_nonneg _
  have he := diskDeformation_sq δ x
  have hx2 : (x : ℝ)^2 ≤ 1 := by nlinarith [hx.1,hx.2]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx2 hδ]

/-- Average the two branches of a measure on the classical radicand domain. -/
noncomputable def diskDeformedMeasure (δ : ℝ)
    (μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}) : Measure ℝ :=
  (1/2 : ℝ≥0) • (μ.map (diskDeformation δ) + μ.map (fun x => -diskDeformation δ x))

instance (δ : ℝ) (μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}) [IsFiniteMeasure μ] :
    IsFiniteMeasure (diskDeformedMeasure δ μ) := by
  unfold diskDeformedMeasure
  infer_instance

instance (δ : ℝ) (μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}) :
    (diskDeformedMeasure δ μ).IsNegInvariant := by
  constructor
  rw [Measure.neg_def, diskDeformedMeasure, Measure.map_smul (hf := measurable_neg.aemeasurable),
    Measure.map_add _ _ measurable_neg,
    Measure.map_map measurable_neg (continuous_diskDeformation δ).measurable,
    Measure.map_map measurable_neg (show Measurable (fun x => -diskDeformation δ x) from
      (continuous_diskDeformation δ).neg.measurable)]
  simp only [Function.comp_def, neg_neg, add_comm]

/-- Every nonzero deformation parameter has finite fibers on its classical domain. -/
theorem finite_fiber_diskDeformation (δ : ℝ) (hδ : δ ≠ 0) (y : ℝ) :
    {x | diskDeformation δ x = y}.Finite := by
  let p : ℝ[X] := C δ * X^2 + C (1-δ-y^2)
  have hp : p ≠ 0 := by
    intro h
    have he := congrArg (fun q : ℝ[X] => q.coeff 2) h
    have hc : p.coeff 2 = δ := by
      change (C δ * X^2 + C (1-δ-y^2) : ℝ[X]).coeff 2 = δ
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C]
      norm_num
    rw [hc, coeff_zero] at he
    exact hδ he
  have hf := Set.Finite.preimage (f := (Subtype.val : {x : ℝ // 0 ≤ 1-δ+δ*x^2} → ℝ))
    Subtype.val_injective.injOn (finite_setOfPred_isRoot hp)
  apply hf.subset
  intro x hx
  change p.eval (x : ℝ) = 0
  have he := diskDeformation_sq δ x
  rw [hx] at he
  simp only [p, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  linarith

/-- Nonzero measure mass survives the symmetric pushforward. -/
theorem diskDeformedMeasure_ne_zero (δ : ℝ)
    {μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}} (hμ : μ ≠ 0) :
    diskDeformedMeasure δ μ ≠ 0 := by
  intro h
  have hmap : μ.map (diskDeformation δ) = 0 := by
    have hh : μ.map (diskDeformation δ) + μ.map (fun x => -diskDeformation δ x) = 0 :=
      (smul_eq_zero.mp h).resolve_left (by norm_num)
    apply le_antisymm _ bot_le
    calc
      _ ≤ μ.map (diskDeformation δ) + μ.map (fun x => -diskDeformation δ x) :=
        Measure.le_add_right le_rfl
      _ = 0 := hh
  exact hμ ((Measure.map_eq_zero_iff (continuous_diskDeformation δ).measurable.aemeasurable).mp hmap)

/-- The symmetric pushforward remains supported on the closed unit interval. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem ae_mem_Icc_diskDeformedMeasure_on_domain {δ : ℝ}
    {μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hx : ∀ᵐ x : {x : ℝ // 0 ≤ 1-δ+δ*x^2} ∂μ, (x : ℝ) ∈ Icc (-1 : ℝ) 1) :
    ∀ᵐ x ∂diskDeformedMeasure δ μ, x ∈ Icc (-1 : ℝ) 1 := by
  unfold diskDeformedMeasure
  apply Measure.ae_smul_measure
  rw [ae_add_measure_iff]
  constructor
  · apply (ae_map_iff (continuous_diskDeformation δ).measurable.aemeasurable measurableSet_Icc).2
    filter_upwards [hx] with x hx
    exact diskDeformation_mem_Icc hδ hδ1 x hx
  · apply (ae_map_iff (show Measurable (fun x => -diskDeformation δ x) from
      (continuous_diskDeformation δ).neg.measurable).aemeasurable measurableSet_Icc).2
    filter_upwards [hx] with x hx
    have hh := diskDeformation_mem_Icc hδ hδ1 x hx
    change -1 ≤ -diskDeformation δ x ∧ -diskDeformation δ x ≤ 1
    constructor <;> linarith [hh.1,hh.2]

/-- A finite compactly supported source retains every polynomial moment. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_diskDeformedMeasure_on_domain {δ : ℝ}
    {μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}} [IsFiniteMeasure μ]
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hx : ∀ᵐ x : {x : ℝ // 0 ≤ 1-δ+δ*x^2} ∂μ, (x : ℝ) ∈ Icc (-1 : ℝ) 1) :
    HasFiniteMoments (diskDeformedMeasure δ μ) := by
  intro p
  have hi := (p.continuous.pow 2).integrableOn_Icc (μ := diskDeformedMeasure δ μ)
    (a := (-1 : ℝ)) (b := 1)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
    (ae_mem_Icc_diskDeformedMeasure_on_domain hδ hδ1 hx)] at hi

/-- Nondegenerate deformations preserve absence of point masses. -/
theorem nullSingletonClass_diskDeformedMeasure_on_domain {δ : ℝ} (hδ : δ ≠ 0)
    (μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}) [NullSingletonClass μ] :
    NullSingletonClass (diskDeformedMeasure δ μ) := by
  constructor
  intro y
  rw [diskDeformedMeasure, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply (continuous_diskDeformation δ).measurable (measurableSet_singleton y),
    Measure.map_apply (show Measurable (fun x => -diskDeformation δ x) from
      (continuous_diskDeformation δ).neg.measurable) (measurableSet_singleton y)]
  have hp : μ ((diskDeformation δ) ⁻¹' {y}) = 0 :=
    (finite_fiber_diskDeformation δ hδ y).measure_zero μ
  have hn : μ ((fun x => -diskDeformation δ x) ⁻¹' {y}) = 0 := by
    have he : (fun x => -diskDeformation δ x) ⁻¹' {y} =
        {x | diskDeformation δ x = -y} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, neg_eq_iff_eq_neg]
    rw [he]
    exact (finite_fiber_diskDeformation δ hδ (-y)).measure_zero μ
  simp [hp,hn]

/-- The radicand domain is measurable. -/
theorem measurableSet_diskDeformationDomain (δ : ℝ) :
    MeasurableSet {x : ℝ | 0 ≤ 1-δ+δ*x^2} :=
  measurableSet_le measurable_const (by fun_prop)

/-- Supported real source coordinates can be regarded as coordinates in the radicand domain. -/
theorem ae_mem_Icc_comap_diskDeformation (δ : ℝ) {μ : Measure ℝ}
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) :
    ∀ᵐ x : {x : ℝ // 0 ≤ 1-δ+δ*x^2} ∂μ.comap Subtype.val,
      (x : ℝ) ∈ Icc (-1 : ℝ) 1 :=
  (ae_restrict_iff_subtype (measurableSet_diskDeformationDomain δ)).mp (ae_restrict_of_ae hx)

/-- Restriction to the radicand domain recovers every real measure in the unit-parameter range. -/
theorem map_comap_diskDeformation {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (μ : Measure ℝ) :
    Measure.map (Subtype.val : {x : ℝ // 0 ≤ 1-δ+δ*x^2} → ℝ) (μ.comap Subtype.val) = μ := by
  have he := map_comap_subtype_coe (s := {x : ℝ | 0 ≤ 1-δ+δ*x^2})
    (measurableSet_diskDeformationDomain δ) μ
  have hs : ∀ᵐ x ∂μ, x ∈ {x : ℝ | 0 ≤ 1-δ+δ*x^2} :=
    Filter.Eventually.of_forall (diskDeformation_radical_nonneg hδ hδ1)
  exact he.trans (Measure.restrict_eq_self_of_ae_mem hs)

/-- Atomlessness passes to the typed source domain. -/
instance nullSingletonClass_comap_diskDeformation (δ : ℝ) (μ : Measure ℝ) [NullSingletonClass μ] :
    NullSingletonClass (μ.comap (Subtype.val : {x : ℝ // 0 ≤ 1-δ+δ*x^2} → ℝ)) := by
  constructor
  intro x
  exact ((MeasurableEmbedding.subtype_coe (measurableSet_diskDeformationDomain δ)).comap_apply μ {x}).trans
    (by simp only [Set.image_singleton, measure_singleton])

/-- Nonzero real source mass is preserved by the unit-parameter domain transport. -/
theorem comap_diskDeformation_ne_zero {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {μ : Measure ℝ} (hμ : μ ≠ 0) :
    μ.comap (Subtype.val : {x : ℝ // 0 ≤ 1-δ+δ*x^2} → ℝ) ≠ 0 := by
  intro h
  have he := map_comap_diskDeformation hδ hδ1 μ
  rw [h, Measure.map_zero] at he
  exact hμ he.symm

/-- A nonzero atomless measure with finite moments has a positive polynomial pairing. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_of_nullSingletonClass {μ : Measure ℝ}
    [NullSingletonClass μ] [NeZero μ] (hμ : HasFiniteMoments μ) :
    HasPositiveDefiniteIntegral μ := by
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  have hn : ∀ᵐ x ∂μ, p.eval x ≠ 0 :=
    (finite_setOfPred_isRoot hp).countable.ae_notMem μ
  apply lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg (p.eval x)))
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (p.eval x)) (hμ p)).mp hz.symm
  have hh : ∀ᵐ x ∂μ, False := by
    filter_upwards [hn,he] with x hx he
    exact hx (sq_eq_zero_iff.mp he)
  exact (NeZero.ne μ) (by simpa using hh)

/-- A nondegenerate finite atomless source gives a positive polynomial pairing. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_diskDeformedMeasure_on_domain {δ : ℝ}
    {μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hμ : μ ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : ∀ᵐ x : {x : ℝ // 0 ≤ 1-δ+δ*x^2} ∂μ, (x : ℝ) ∈ Icc (-1 : ℝ) 1) :
    HasPositiveDefiniteIntegral (diskDeformedMeasure δ μ) := by
  let := nullSingletonClass_diskDeformedMeasure_on_domain hδ.ne' μ
  let : NeZero (diskDeformedMeasure δ μ) := ⟨diskDeformedMeasure_ne_zero δ hμ⟩
  exact hasPositiveDefiniteIntegral_of_nullSingletonClass
    (hasFiniteMoments_diskDeformedMeasure_on_domain hδ.le hδ1 hx)

/-- Continuous functions integrate by averaging their two classical branch pullbacks. -/
theorem integral_diskDeformedMeasure (δ : ℝ)
    {μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x : {x : ℝ // 0 ≤ 1-δ+δ*x^2} ∂μ, (x : ℝ) ∈ Icc (-1 : ℝ) 1)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂diskDeformedMeasure δ μ =
      (1/2 : ℝ) * (∫ t, f (diskDeformation δ t) ∂μ) +
      (1/2 : ℝ) * (∫ t, f (-diskDeformation δ t) ∂μ) := by
  have hclosed : IsClosed {x : ℝ | 0 ≤ 1-δ+δ*x^2} :=
    isClosed_le continuous_const (by fun_prop)
  have hcompact : IsCompact
      (Subtype.val ⁻¹' Icc (-1 : ℝ) 1 : Set {x : ℝ // 0 ≤ 1-δ+δ*x^2}) :=
    hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_Icc
  have hi {g : {x : ℝ // 0 ≤ 1-δ+δ*x^2} → ℝ} (hg : Continuous g) :
      Integrable g μ := by
    have hh := hg.continuousOn.integrableOn_compact (μ := μ) hcompact
    have hx' : ∀ᵐ x ∂μ, x ∈ Subtype.val ⁻¹' Icc (-1 : ℝ) 1 := hx
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hx'] at hh
  have hp0 : Integrable (fun x => f (diskDeformation δ x)) μ :=
    hi (hf.comp (continuous_diskDeformation δ))
  have hn0 : Integrable (fun x => f (-diskDeformation δ x)) μ :=
    hi (hf.comp (continuous_diskDeformation δ).neg)
  have hp := (integrable_map_measure hf.aestronglyMeasurable
    (continuous_diskDeformation δ).measurable.aemeasurable).2 hp0
  have hn := (integrable_map_measure hf.aestronglyMeasurable
    (show Measurable (fun x => -diskDeformation δ x) from
      (continuous_diskDeformation δ).neg.measurable).aemeasurable).2 hn0
  rw [diskDeformedMeasure, integral_smul_nnreal_measure, integral_add_measure hp hn,
    integral_map (continuous_diskDeformation δ).measurable.aemeasurable hf.aestronglyMeasurable,
    integral_map (show Measurable (fun x => -diskDeformation δ x) from
      (continuous_diskDeformation δ).neg.measurable).aemeasurable hf.aestronglyMeasurable]
  norm_num [NNReal.smul_def, smul_eq_mul, mul_add]

/-- Integrable real inputs transport to the full classical deformation domain. -/
theorem integral_comap_diskDeformation {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (μ : Measure ℝ) (f : IntegrableInput μ) :
    ∫ x : {x : ℝ // 0 ≤ 1-δ+δ*x^2}, f.val (x : ℝ) ∂μ.comap Subtype.val =
      ∫ x, f.val x ∂μ := by
  have he := map_comap_diskDeformation hδ hδ1 μ
  have hm : AEStronglyMeasurable f.val
      (Measure.map (Subtype.val : {x : ℝ // 0 ≤ 1-δ+δ*x^2} → ℝ)
        (μ.comap Subtype.val)) := by
    rw [he]
    exact f.property.aestronglyMeasurable
  exact (integral_map measurable_subtype_coe.aemeasurable hm).symm.trans
    (by rw [he])

/-- Real supported source measures have the same classical branch formula. -/
theorem integral_diskDeformedMeasure_comap {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂diskDeformedMeasure δ (μ.comap Subtype.val) =
      (1/2 : ℝ) * (∫ t, f (diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩) ∂μ) +
      (1/2 : ℝ) * (∫ t, f (-diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩) ∂μ) := by
  rw [integral_diskDeformedMeasure δ (ae_mem_Icc_comap_diskDeformation δ hx) hf]
  have hc : Continuous (fun t : ℝ =>
      diskDeformation δ ⟨t, diskDeformation_radical_nonneg hδ hδ1 t⟩) :=
    (continuous_diskDeformation δ).comp (continuous_id.subtype_mk _)
  have hi {g : ℝ → ℝ} (hg : Continuous g) : Integrable g μ := by
    have hh := hg.integrableOn_Icc (μ := μ) (a := (-1 : ℝ)) (b := 1)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hx] at hh
  exact congrArg₂ (fun a b : ℝ => (1/2 : ℝ)*a+(1/2 : ℝ)*b)
    (integral_comap_diskDeformation hδ hδ1 μ
      ⟨_, hi (hf.comp hc)⟩)
    (integral_comap_diskDeformation hδ hδ1 μ
      ⟨_, hi (hf.comp hc.neg)⟩)

/-- Classical squared-coordinate identity for a unit-interval parameter and any real input. -/
theorem diskDeformation_sq_of_unitInterval {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : ℝ) :
    diskDeformation δ ⟨x,diskDeformation_radical_nonneg hδ hδ1 x⟩ ^ 2 = 1-δ+δ*x^2 :=
  diskDeformation_sq δ _

/-- Supported real coordinates remain in the unit interval under deformation. -/
theorem diskDeformation_mem_Icc_of_unitInterval {δ x : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    diskDeformation δ ⟨x,diskDeformation_radical_nonneg hδ hδ1 x⟩ ∈ Icc (-1 : ℝ) 1 :=
  diskDeformation_mem_Icc hδ hδ1 _ hx

/-- The deformed transport of a supported real measure has unit-interval support. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem ae_mem_Icc_diskDeformedMeasure {μ : Measure ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) :
    ∀ᵐ x ∂diskDeformedMeasure δ (μ.comap Subtype.val), x ∈ Icc (-1 : ℝ) 1 :=
  ae_mem_Icc_diskDeformedMeasure_on_domain hδ hδ1 (ae_mem_Icc_comap_diskDeformation δ hx)

/-- Finite supported real source measures retain all polynomial moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_diskDeformedMeasure {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) :
    HasFiniteMoments (diskDeformedMeasure δ (μ.comap Subtype.val)) :=
  hasFiniteMoments_diskDeformedMeasure_on_domain hδ hδ1 (ae_mem_Icc_comap_diskDeformation δ hx)

/-- Atomlessness survives supported real-measure transport and nondegenerate deformation. -/
theorem nullSingletonClass_diskDeformedMeasure {μ : Measure ℝ} [NullSingletonClass μ]
    {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) :
    NullSingletonClass (diskDeformedMeasure δ (μ.comap Subtype.val)) :=
  nullSingletonClass_diskDeformedMeasure_on_domain hδ.ne' _

/-- A nonzero finite atomless real source gives a positive deformed polynomial pairing. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_diskDeformedMeasure {μ : Measure ℝ}
    [IsFiniteMeasure μ] [NullSingletonClass μ] (hμ : μ ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) :
    HasPositiveDefiniteIntegral (diskDeformedMeasure δ (μ.comap Subtype.val)) :=
  hasPositiveDefiniteIntegral_diskDeformedMeasure_on_domain
    (comap_diskDeformation_ne_zero hδ.le hδ1 hμ) hδ hδ1 (ae_mem_Icc_comap_diskDeformation δ hx)

/-- Even test functions have a single classical branch integral. -/
theorem integral_diskDeformedMeasure_even (δ : ℝ)
    {μ : Measure {x : ℝ // 0 ≤ 1-δ+δ*x^2}} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x : {x : ℝ // 0 ≤ 1-δ+δ*x^2} ∂μ, (x : ℝ) ∈ Icc (-1 : ℝ) 1)
    {f : ℝ → ℝ} (hf : Continuous f) (he : Function.Even f) :
    ∫ x, f x ∂diskDeformedMeasure δ μ = ∫ t, f (diskDeformation δ t) ∂μ := by
  rw [integral_diskDeformedMeasure δ hx hf]
  have heq : (fun t => f (-diskDeformation δ t)) = (fun t => f (diskDeformation δ t)) := _root_.funext (fun t => he (diskDeformation δ t))
  rw [heq]
  ring

/-- The disk squared scale acquires a factor of the deformation parameter. -/
theorem one_sub_diskDeformation_sq {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : ℝ) :
    1-diskDeformation δ ⟨x,diskDeformation_radical_nonneg hδ hδ1 x⟩^2 = δ*(1-x^2) := by
  rw [diskDeformation_sq_of_unitInterval hδ hδ1]
  ring

/-- The degree-shifted outer integral acquires exactly the factor `δ^k`. -/
theorem integral_diskOuterMeasure_diskDeformedMeasure {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val) =
      δ^k * ((1/2 : ℝ) * (∫ t, f (diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩) ∂diskOuterMeasure k (μ.comap Subtype.val)) +
        (1/2 : ℝ) * (∫ t, f (-diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩) ∂diskOuterMeasure k (μ.comap Subtype.val))) := by
  have hc : Continuous (fun t : ℝ =>
      diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩) :=
    (continuous_diskDeformation δ).comp (continuous_id.subtype_mk _)
  have hx' := ae_mem_Icc_diskDeformedMeasure hδ hδ1 hx
  erw [integral_diskOuterMeasure _ hx' k
      ⟨f, integrable_diskOuterMeasure_of_continuous hx' k hf⟩,
    integral_diskDeformedMeasure_comap hx hδ hδ1 (by
      change Continuous (fun x : ℝ => (1-x^2)^k*f x)
      fun_prop),
    integral_diskOuterMeasure μ hx k
      ⟨fun t => f (diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩),
        integrable_diskOuterMeasure_of_continuous hx k (hf.comp hc)⟩,
    integral_diskOuterMeasure μ hx k
      ⟨fun t => f (-diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩),
        integrable_diskOuterMeasure_of_continuous hx k (hf.comp hc.neg)⟩]
  dsimp only
  simp_rw [neg_sq, one_sub_diskDeformation_sq hδ hδ1, mul_pow, mul_assoc,
    integral_const_mul]
  ring

/-- The even shifted integral is a single pullback, scaled by `δ^k`. -/
theorem integral_diskOuterMeasure_diskDeformedMeasure_even
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) (he : Function.Even f) :
    ∫ x, f x ∂diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val) =
      δ^k * (∫ t, f (diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩) ∂diskOuterMeasure k (μ.comap Subtype.val)) := by
  rw [integral_diskOuterMeasure_diskDeformedMeasure hx hδ hδ1 k hf]
  have heq : (fun t => f (-diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩)) =
      (fun t => f (diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩))  := _root_.funext (fun t => he (diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩))
  rw [heq]
  ring


/-- Deformation of a supported source transports through the closed classical interval. -/
theorem comap_diskDeformedMeasure {μ : Measure ℝ} (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (diskDeformedMeasure δ (μ.comap Subtype.val)).comap
      (Subtype.val : Icc (-1 : ℝ) 1 → ℝ) =
    (1/2 : ℝ≥0) •
      (Measure.map (fun x : Icc (-1 : ℝ) 1 =>
        (⟨diskDeformation δ ⟨x, diskDeformation_radical_nonneg hδ hδ1 x⟩,
          diskDeformation_mem_Icc hδ hδ1 _ x.property⟩ : Icc (-1 : ℝ) 1))
        (μ.comap Subtype.val) +
       Measure.map (fun x : Icc (-1 : ℝ) 1 =>
        (⟨-diskDeformation δ ⟨x, diskDeformation_radical_nonneg hδ hδ1 x⟩,
          by have h := diskDeformation_mem_Icc hδ hδ1
               ⟨(x : ℝ), diskDeformation_radical_nonneg hδ hδ1 x⟩ x.property
             constructor <;> linarith [h.1,h.2]⟩ : Icc (-1 : ℝ) 1))
        (μ.comap Subtype.val)) := by
  let r (t : ℝ) := diskDeformation δ ⟨t, diskDeformation_radical_nonneg hδ hδ1 t⟩
  have hr : Continuous r :=
    (continuous_diskDeformation δ).comp (continuous_id.subtype_mk _)
  have hm (g : ℝ → ℝ) (hg : Measurable g) :
      Measure.map (fun x : {x : ℝ // 0 ≤ 1-δ+δ*x^2} => g x)
        (μ.comap Subtype.val) = Measure.map g μ := by
    erw [← Measure.map_map hg measurable_subtype_coe, map_comap_diskDeformation hδ hδ1]
  have hc (g : ℝ → ℝ) (hg : Measurable g) :
      Measure.map (fun x : Icc (-1 : ℝ) 1 => g x)
        (μ.comap Subtype.val) = Measure.map g μ := by
    erw [← Measure.map_map hg measurable_subtype_coe,
      map_comap_subtype_coe measurableSet_Icc, Measure.restrict_eq_self_of_ae_mem hx]
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [map_comap_subtype_coe measurableSet_Icc,
    Measure.restrict_eq_self_of_ae_mem (ae_mem_Icc_diskDeformedMeasure hδ hδ1 hx)]
  erw [Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    Measure.map_add _ _ measurable_subtype_coe,
    Measure.map_map measurable_subtype_coe
      ((hr.comp continuous_subtype_val).subtype_mk _).measurable,
    Measure.map_map measurable_subtype_coe
      ((hr.neg.comp continuous_subtype_val).subtype_mk _).measurable]
  change (1/2 : ℝ≥0) •
      (Measure.map (fun x : {x : ℝ // 0 ≤ 1-δ+δ*x^2} => r x) (μ.comap Subtype.val) +
       Measure.map (fun x : {x : ℝ // 0 ≤ 1-δ+δ*x^2} => -r x) (μ.comap Subtype.val)) =
    (1/2 : ℝ≥0) •
      (Measure.map (fun x : Icc (-1 : ℝ) 1 => r x) (μ.comap Subtype.val) +
       Measure.map (fun x : Icc (-1 : ℝ) 1 => -r x) (μ.comap Subtype.val))
  rw [hm r hr.measurable, hm (fun x => -r x) hr.neg.measurable,
    hc r hr.measurable, hc (fun x => -r x) hr.neg.measurable]

end Polynomial
