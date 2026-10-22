/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Modification
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Polynomial densities for separated disk modifications

The modification is defined as an actual bivariate polynomial and identified
with the product of modified one-dimensional measures by integration.
Reference: Dunkl–Xu, Cartesian construction; Gutleb–Olver–Slevinsky,
polynomial modification identities.
-/

@[expose] public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- The actual polynomial representing a separated modification on the disk. -/
noncomputable def cartesianDiskModification (h g : ℝ[X]) (l : ℕ) : MvPolynomial (Fin 2) ℝ :=
  cartesianDiskPolynomial h g (2*l)

/-- The separated density formula, valid even at the vertical boundary. -/
theorem eval_cartesianDiskModification (h g : ℝ[X]) (l : ℕ)
    (hgdeg : g.natDegree ≤ 2*l) (hgpar : ∀ i, i % 2 ≠ 0 → g.coeff i = 0)
    (x z : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (x,z)) (cartesianDiskModification h g l) =
      (diskModificationWeight h l).eval x * g.eval z := by
  rw [cartesianDiskModification, eval_cartesianDiskPolynomial h g (2*l) hgdeg
    (by simpa using hgpar) x z hx, pow_mul,
    Real.sq_sqrt (by nlinarith [hx.1,hx.2] : 0 ≤ 1-x^2)]
  simp [diskModificationWeight,mul_comm]

/-- Changing the two separated factors multiplies every continuous test integral
by the stated bivariate polynomial. -/
theorem integral_cartesianDiskModification {μ ν : Measure ℝ}
    (hμ : Polynomial.HasFiniteMoments μ) (hν : Polynomial.HasFiniteMoments ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)
    (h g : ℝ[X]) (l : ℕ) (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x)
    (hg : ∀ᵐ z ∂ν, 0 ≤ g.eval z) (hgdeg : g.natDegree ≤ 2*l)
    (hgpar : ∀ i, i % 2 ≠ 0 → g.coeff i = 0)
    {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    ∫ v, f v ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
      (ProductMeasureInput.ofSFinite (hν := by let := hν.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val))) (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val))) =
      ∫ v, eval v (cartesianDiskModification h g l)*f v ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (hν := by let := hν.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) := by
  let := hμ.isFiniteMeasure
  let := hν.isFiniteMeasure
  let := (hμ.diskOuterModification hx h hh l).isFiniteMeasure
  let := (hν.polynomialDensityMeasure g hg).isFiniteMeasure
  have hz' : ∀ᵐ z ∂Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val),
      z ∈ Icc (-1 : ℝ) 1 := (polynomialDensityMeasure_comap_absolutelyContinuous g ν).ae_le hz
  have hh' : ∀ᵐ x : Icc (-1 : ℝ) 1 ∂μ.comap Subtype.val,
      0 ≤ h.eval (x : ℝ) := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le measurable_const h.continuous.measurable)).mp
    rwa [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem hx]
  obtain ⟨w, hw, hwval, _, hwmeasure⟩ :=
    exists_subtypeDensityMeasure_extension (D := Icc (-1 : ℝ) 1)
      (diskModificationWeight h l)
  obtain ⟨v, hv, hvval, _, hvmeasure⟩ := exists_polynomialDensityMeasure_extension g
  rw [integral_cartesianDiskMeasure_eq_iterated
      (ae_mem_diskOuterModification hx h l) hz' hf,
    integral_cartesianDiskMeasure_eq_iterated hx hz
      (show Continuous (fun v => eval v (cartesianDiskModification h g l)*f v) from
        (cartesianDiskModification h g l).continuous_eval.mul hf),
    diskOuterModification,
    comap_polynomialDensityMeasure_eq_subtypeDensityMeasure measurableSet_Icc _ μ hx,
    hwmeasure, integral_withDensity_eq_integral_toReal_smul hw.coe_nnreal_ennreal
      (Filter.Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  apply integral_congr_ae
  filter_upwards [hh'] with x hhx
  have hweight : 0 ≤ (diskModificationWeight h l).eval (x : ℝ) := by
    simp only [diskModificationWeight, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
    exact mul_nonneg (pow_nonneg (diskCoordinates_sq_nonneg x) _) hhx
  rw [hwval x hweight]
  simp only [ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul]
  rw [hvmeasure, integral_withDensity_eq_integral_toReal_smul hv.coe_nnreal_ennreal
      (Filter.Eventually.of_forall (fun _ => ENNReal.coe_lt_top)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hg] with z hz
  rw [hvval z hz]
  simp only [ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul]
  change _ = eval (![ (x : ℝ), Real.sqrt (1-(x : ℝ)^2)*z])
    (cartesianDiskModification h g l) * _
  rw [eval_cartesianDiskModification h g l hgdeg hgpar (x : ℝ) z x.property]
  ring

/-- The modified polynomial pairing is multiplication by the separated density. -/
theorem integralInner_cartesianDiskModification {μ ν : Measure ℝ}
    (hμ : Polynomial.HasFiniteMoments μ) (hν : Polynomial.HasFiniteMoments ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)
    (h g : ℝ[X]) (l : ℕ) (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x)
    (hg : ∀ᵐ z ∂ν, 0 ≤ g.eval z) (hgdeg : g.natDegree ≤ 2*l)
    (hgpar : ∀ i, i % 2 ≠ 0 → g.coeff i = 0) (p q : MvPolynomial (Fin 2) ℝ) :
    integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
      (ProductMeasureInput.ofSFinite (hν := by let := hν.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val))) (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
      (ProductMeasureInput.ofSFinite (hν := by let := hν.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val))) (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))) p q) =
      integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (hν := by let := hν.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (hν := by let := hν.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (cartesianDiskModification h g l*p) q) := by
  rw [integralInner, integral_cartesianDiskModification hμ hν hx hz h g l hh hg hgdeg hgpar
    (show Continuous (fun v => eval v p*eval v q) from p.continuous_eval.mul q.continuous_eval)]
  simp only [integralInner,map_mul,mul_assoc]

end MvPolynomial
