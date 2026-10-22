/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Deformation
public import LeanFun.Mathlib.RingTheory.Polynomial.EvenTransport
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.LinearCombination
/-!
# Cartesian pullback under deformation

The normalized transported polynomials agree on corresponding disk slices.
Quadratic modifications pull back to an affine pencil in the deformation parameter.
Reference: Dunkl–Xu, §2.6.1 and Chapter 3.
-/

public section
open MeasureTheory Set Polynomial
open scoped NNReal ENNReal
namespace MvPolynomial

/-- The outer normalization exactly cancels the even inner-lift scaling. -/
theorem eval_cartesianDiskPolynomial_evenDiskTransport
    {δ : ℝ} (hδ : 0 < δ) (b : ℕ) (p q : ℝ[X])
    (hp : ∀ i, i % 2 ≠ 0 → p.coeff i = 0)
    (hq : q.natDegree ≤ 2*b) (hpar : ∀ j, j % 2 ≠ (2*b) % 2 → q.coeff j = 0)
    (x t z : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hxt : x^2 = 1-δ+δ*t^2) :
    eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (x,z))
      (cartesianDiskPolynomial (δ⁻¹^b • evenDiskTransport ⟨δ,hδ.ne'⟩ p) q (2*b)) =
    eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (t,z)) (cartesianDiskPolynomial p q (2*b)) := by
  rw [eval_cartesianDiskPolynomial _ _ _ hq hpar x z hx,
    eval_cartesianDiskPolynomial _ _ _ hq hpar t z ht, Polynomial.eval_smul,
    smul_eq_mul, eval_evenDiskTransport_sq δ hδ.ne' p hp x t hxt]
  have hx0 : 0 ≤ 1-x^2 := by nlinarith [hx.1,hx.2]
  have ht0 : 0 ≤ 1-t^2 := by nlinarith [ht.1,ht.2]
  have he : 1-x^2 = δ*(1-t^2) := by rw [hxt]; ring
  rw [pow_mul, pow_mul, Real.sq_sqrt hx0, Real.sq_sqrt ht0, he, mul_pow]
  have hc : δ⁻¹^b * δ^b = 1 := by rw [← mul_pow, inv_mul_cancel₀ hδ.ne', one_pow]
  linear_combination p.eval t * (1-t^2)^b * q.eval z * hc

/-- Disk integration is the average of the two deformed Cartesian branches. -/
theorem integral_cartesianDiskMeasure_diskDeformedMeasure
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    ∫ v, f v ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ (μ.comap Subtype.val))) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ (μ.comap Subtype.val))) ν) =
      (1/2 : ℝ) * (∫ t : Icc (-1 : ℝ) 1, ∫ z, f ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩,z)) ∂ν ∂μ.comap Subtype.val) +
      (1/2 : ℝ) * (∫ t : Icc (-1 : ℝ) 1, ∫ z, f ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (-diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩,z)) ∂ν ∂μ.comap Subtype.val) := by
  rw [integral_cartesianDiskMeasure_eq_iterated
    (ae_mem_Icc_diskDeformedMeasure hδ hδ1 hx) hz hf]
  have hc : Continuous (fun t : Icc (-1 : ℝ) 1 =>
      diskDeformation δ ⟨(t : ℝ), diskDeformation_radical_nonneg hδ hδ1 t⟩) :=
    (continuous_diskDeformation δ).comp (continuous_subtype_val.subtype_mk _)
  have hrange (t : Icc (-1 : ℝ) 1) :
      diskDeformation δ ⟨(t : ℝ), diskDeformation_radical_nonneg hδ hδ1 t⟩ ∈
        Icc (-1 : ℝ) 1 := diskDeformation_mem_Icc hδ hδ1 _ t.property
  have hlrange (t : Icc (-1 : ℝ) 1) :
      -diskDeformation δ ⟨(t : ℝ), diskDeformation_radical_nonneg hδ hδ1 t⟩ ∈
        Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [(hrange t).1, (hrange t).2]
  let r : C(Icc (-1 : ℝ) 1, Icc (-1 : ℝ) 1) :=
    ⟨fun t => ⟨diskDeformation δ ⟨t, diskDeformation_radical_nonneg hδ hδ1 t⟩,
      hrange t⟩, hc.subtype_mk hrange⟩
  let l : C(Icc (-1 : ℝ) 1, Icc (-1 : ℝ) 1) :=
    ⟨fun t => ⟨-diskDeformation δ ⟨t, diskDeformation_radical_nonneg hδ hδ1 t⟩,
      hlrange t⟩, hc.neg.subtype_mk hlrange⟩
  let F : Icc (-1 : ℝ) 1 → ℝ := fun x => ∫ z, f (diskCoordinates (x,z)) ∂ν
  have hF : Continuous F := by
    have hc := continuous_parametric_integral_of_continuous
      (μ := ν) (f := fun x : Icc (-1 : ℝ) 1 => fun z => f (diskCoordinates (x,z)))
      (hf.comp continuous_diskCoordinates) (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
    simpa only [Measure.restrict_eq_self_of_ae_mem hz] using hc
  have hi (η : Measure (Icc (-1 : ℝ) 1)) [IsFiniteMeasure η] : Integrable F η := by
    simpa using hF.continuousOn.integrableOn_compact (μ := η) isCompact_univ
  rw [comap_diskDeformedMeasure hx hδ hδ1]
  change (∫ x, F x ∂(1/2 : ℝ≥0) •
      (Measure.map r (μ.comap Subtype.val) + Measure.map l (μ.comap Subtype.val))) =
    (1/2 : ℝ) * (∫ t, F (r t) ∂μ.comap Subtype.val) +
    (1/2 : ℝ) * (∫ t, F (l t) ∂μ.comap Subtype.val)
  rw [integral_smul_nnreal_measure, integral_add_measure (hi _) (hi _),
    integral_map r.continuous.measurable.aemeasurable hF.aestronglyMeasurable,
    integral_map l.continuous.measurable.aemeasurable hF.aestronglyMeasurable]
  norm_num [NNReal.smul_def, smul_eq_mul, mul_add]

/-- Under matching branch values, a quadratic modified integral becomes an affine pencil. -/
theorem integral_quadratic_diskDeformedMeasure
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (A B C : ℝ)
    {f g : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hp : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
      f ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩,z)) = g ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (t,z)))
    (hm : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
      f ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (-diskDeformation δ ⟨t,diskDeformation_radical_nonneg hδ hδ1 t⟩,z)) = g ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (t,z))) :
    ∫ v, (A+B*(v 0)^2+C*(v 1)^2)*f v ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ (μ.comap Subtype.val))) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ (μ.comap Subtype.val))) ν) =
      ∫ v, ((A+B)+δ*(C*(v 1)^2-B*(1-(v 0)^2)))*g v ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) := by
  have hc : Continuous (fun t : Icc (-1 : ℝ) 1 =>
      diskDeformation δ ⟨(t : ℝ), diskDeformation_radical_nonneg hδ hδ1 t⟩) :=
    (continuous_diskDeformation δ).comp (continuous_subtype_val.subtype_mk _)
  have hrange (t : Icc (-1 : ℝ) 1) :
      diskDeformation δ ⟨(t : ℝ), diskDeformation_radical_nonneg hδ hδ1 t⟩ ∈
        Icc (-1 : ℝ) 1 := diskDeformation_mem_Icc hδ hδ1 _ t.property
  have hlrange (t : Icc (-1 : ℝ) 1) :
      -diskDeformation δ ⟨(t : ℝ), diskDeformation_radical_nonneg hδ hδ1 t⟩ ∈
        Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [(hrange t).1, (hrange t).2]
  let r : C(Icc (-1 : ℝ) 1, Icc (-1 : ℝ) 1) :=
    ⟨fun t => ⟨diskDeformation δ ⟨t, diskDeformation_radical_nonneg hδ hδ1 t⟩,
      hrange t⟩, hc.subtype_mk hrange⟩
  let l : C(Icc (-1 : ℝ) 1, Icc (-1 : ℝ) 1) :=
    ⟨fun t => ⟨-diskDeformation δ ⟨t, diskDeformation_radical_nonneg hδ hδ1 t⟩,
      hlrange t⟩, hc.neg.subtype_mk hlrange⟩
  let F : (Fin 2 → ℝ) → ℝ := fun v => (A+B*(v 0)^2+C*(v 1)^2)*f v
  let G : (Fin 2 → ℝ) → ℝ := fun v => ((A+B)+δ*(C*(v 1)^2-B*(1-(v 0)^2)))*g v
  rw [integral_cartesianDiskMeasure_diskDeformedMeasure hx hz hδ hδ1 (by fun_prop),
    integral_cartesianDiskMeasure_eq_iterated hx hz (by fun_prop)]
  change (1/2 : ℝ) * (∫ t, ∫ z, F (diskCoordinates (r t,z)) ∂ν ∂μ.comap Subtype.val) +
      (1/2 : ℝ) * (∫ t, ∫ z, F (diskCoordinates (l t,z)) ∂ν ∂μ.comap Subtype.val) =
    ∫ t, ∫ z, G (diskCoordinates (t,z)) ∂ν ∂μ.comap Subtype.val
  have hb (ψ : C(Icc (-1 : ℝ) 1, Icc (-1 : ℝ) 1))
      (hψ : ∀ t, (ψ t : ℝ)^2 = 1-δ+δ*(t : ℝ)^2)
      (he : ∀ t, ∀ z ∈ Icc (-1 : ℝ) 1,
        f (diskCoordinates (ψ t,z)) = g (diskCoordinates (t,z))) :
      (∫ t, ∫ z, F (diskCoordinates (ψ t,z)) ∂ν ∂μ.comap Subtype.val) =
        ∫ t, ∫ z, G (diskCoordinates (t,z)) ∂ν ∂μ.comap Subtype.val := by
    apply integral_congr_ae
    filter_upwards [] with t
    apply integral_congr_ae
    filter_upwards [hz] with z hz
    dsimp only [F,G]
    rw [he t z hz]
    simp only [diskCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_pow, Real.sq_sqrt (diskCoordinates_sq_nonneg t),
      Real.sq_sqrt (diskCoordinates_sq_nonneg (ψ t))]
    rw [hψ]
    ring
  rw [hb r (fun t => diskDeformation_sq_of_unitInterval hδ hδ1 t)
      (fun t z hz => hp t t.property z hz),
    hb l (fun t => by
      change (-diskDeformation δ ⟨(t : ℝ), diskDeformation_radical_nonneg hδ hδ1 t⟩)^2 = _
      simpa only [neg_sq] using diskDeformation_sq_of_unitInterval hδ hδ1 (t : ℝ))
      (fun t z hz => hm t t.property z hz)]
  ring

end MvPolynomial
