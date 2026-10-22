/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Measure
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Separated pairings for Cartesian disk products

Inner orthogonality separates from the degree-dependent outer pairing.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- Integrable separated factors give an integrable Cartesian pair. -/
theorem integrable_cartesianDiskPolynomial_mul {μ ν : Measure ℝ}
    [SFinite μ] [SFinite ν] (_hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (p q r s : ℝ[X]) (k j : ℕ) (hr : r.natDegree ≤ k) (hs : s.natDegree ≤ j)
    (hpr : ∀ i, i % 2 ≠ k % 2 → r.coeff i = 0)
    (hps : ∀ i, i % 2 ≠ j % 2 → s.coeff i = 0)
    (ho : Integrable (fun x : Icc (-1 : ℝ) 1 => p.eval (x : ℝ)*q.eval (x : ℝ)*Real.sqrt (1-(x : ℝ)^2)^(k+j)) (μ.comap Subtype.val))
    (hi : Integrable (fun z => r.eval z*s.eval z) ν) :
    Integrable (fun v => eval v (cartesianDiskPolynomial p r k) *
      eval v (cartesianDiskPolynomial q s j)) (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) := by
  change Integrable _ (Measure.map diskCoordinates ((μ.comap Subtype.val).prod ν))
  erw [integrable_map_measure
    ((cartesianDiskPolynomial p r k).continuous_eval.mul
      (cartesianDiskPolynomial q s j).continuous_eval).aestronglyMeasurable
    continuous_diskCoordinates.measurable.aemeasurable]
  apply (ho.mul_prod hi).congr
  filter_upwards [] with v
  dsimp only [Function.comp_apply, diskCoordinates, Pi.mul_apply]
  rw [eval_cartesianDiskPolynomial p r k hr hpr v.1 v.2 v.1.property,
    eval_cartesianDiskPolynomial q s j hs hps v.1 v.2 v.1.property, pow_add]
  ring

/-- An even degree gap transports integrability from the shifted outer measure. -/
theorem integrable_disk_outer_factor {μ : Measure ℝ}
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (p q : ℝ[X])
    (k j r : ℕ) (hkj : k=j+2*r)
    (hi : Integrable (fun x => ((1-Polynomial.X^2)^r*p).eval x*q.eval x)
      (diskOuterMeasure j (μ.comap Subtype.val))) :
    Integrable (fun x : Icc (-1 : ℝ) 1 => p.eval (x : ℝ)*q.eval (x : ℝ)*Real.sqrt (1-(x : ℝ)^2)^(k+j)) (μ.comap Subtype.val) := by
  have hu : ∀ᵐ x ∂μ, 0 ≤ ((1-Polynomial.X^2 : ℝ[X])^j).eval x := by
    filter_upwards [hx] with x hx
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
    exact pow_nonneg (by nlinarith [hx.1,hx.2]) j
  have hw := (integrable_polynomialDensityMeasure_comap_iff
    ((1-Polynomial.X^2)^j) hu _).mp hi
  have hm : Measure.map (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
      (μ.comap Subtype.val) = μ := by
    rw [map_comap_subtype_coe measurableSet_Icc, Measure.restrict_eq_self_of_ae_mem hx]
  rw [← hm] at hw
  apply (hw.comp_measurable measurable_subtype_coe).congr
  filter_upwards [] with x
  dsimp only [Function.comp_apply]
  rw [show k+j=2*(j+r) by omega, pow_mul,
    Real.sq_sqrt (diskCoordinates_sq_nonneg x)]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, pow_add]
  ring

/-- Arbitrary Cartesian polynomial pairings separate into two one-dimensional integrals. -/
theorem integralInner_cartesianDiskPolynomial {μ ν : Measure ℝ}
    [SFinite μ] [SFinite ν] (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (p q r s : ℝ[X]) (k j : ℕ) (hr : r.natDegree ≤ k) (hs : s.natDegree ≤ j)
    (hpr : ∀ i, i % 2 ≠ k % 2 → r.coeff i = 0)
    (hps : ∀ i, i % 2 ≠ j % 2 → s.coeff i = 0)
    (ho : Integrable (fun x : Icc (-1 : ℝ) 1 => p.eval (x : ℝ)*q.eval (x : ℝ)*Real.sqrt (1-(x : ℝ)^2)^(k+j)) (μ.comap Subtype.val) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hi : Integrable (fun z => r.eval z*s.eval z) ν := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (cartesianDiskPolynomial p r k) (cartesianDiskPolynomial q s j)
      (h := by
        exact integrable_cartesianDiskPolynomial_mul (μ := μ) (ν := ν) hx p q r s k j hr hs hpr hps ho hi)) =
      (∫ x : Icc (-1 : ℝ) 1, p.eval (x : ℝ) * q.eval (x : ℝ) * Real.sqrt (1-(x : ℝ)^2)^(k+j) ∂μ.comap Subtype.val) *
        Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν r s (h := hi)) := by
  let : SFinite (μ.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)) := by
    refine ⟨⟨fun n => (sfiniteSeq μ n).comap Subtype.val, fun n => inferInstance, ?_⟩⟩
    ext t ht
    rw [Measure.sum_apply _ ht]
    simp only [comap_subtype_coe_apply measurableSet_Icc]
    rw [← Measure.sum_apply _ ((MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image.mpr ht),
      sum_sfiniteSeq]
  simp only [integralInner, Polynomial.integralInner]
  change (∫ v, eval v (cartesianDiskPolynomial p r k) *
      eval v (cartesianDiskPolynomial q s j)
      ∂Measure.map diskCoordinates ((μ.comap Subtype.val).prod ν)) = _
  erw [integral_map continuous_diskCoordinates.measurable.aemeasurable
    ((cartesianDiskPolynomial p r k).continuous_eval.mul
      (cartesianDiskPolynomial q s j).continuous_eval).aestronglyMeasurable,
    ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  dsimp only [diskCoordinates, Pi.mul_apply]
  rw [eval_cartesianDiskPolynomial p r k hr hpr v.1 v.2 v.1.property,
    eval_cartesianDiskPolynomial q s j hs hps v.1 v.2 v.1.property, pow_add]
  ring

/-- Equal lift degrees turn the outer factor into a polynomial density shift. -/
theorem integralInner_cartesianDiskPolynomial_same_degree {μ ν : Measure ℝ}
    [SFinite μ] [SFinite ν] (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (p q r s : ℝ[X]) (k : ℕ) (hr : r.natDegree ≤ k) (hs : s.natDegree ≤ k)
    (hpr : ∀ i, i % 2 ≠ k % 2 → r.coeff i = 0)
    (hps : ∀ i, i % 2 ≠ k % 2 → s.coeff i = 0)
    (ho : Integrable (fun x => p.eval x*q.eval x) (diskOuterMeasure k (μ.comap Subtype.val)) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hi : Integrable (fun z => r.eval z*s.eval z) ν := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (cartesianDiskPolynomial p r k) (cartesianDiskPolynomial q s k) (h := by
        exact integrable_cartesianDiskPolynomial_mul (μ := μ) (ν := ν)
          hx p q r s k k hr hs hpr hps
          (integrable_disk_outer_factor (μ := μ) hx p q k k 0 (by omega) (by simpa using ho)) hi)) =
      Polynomial.integralInner (diskOuterMeasure k (μ.comap Subtype.val)) (Polynomial.IntegrablePair.of (diskOuterMeasure k (μ.comap Subtype.val)) p q (h := by simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_X] using ho)) *
        Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν r s (h := hi)) := by
  rw [integralInner_cartesianDiskPolynomial hx p q r s k k hr hs hpr hps
    (integrable_disk_outer_factor (μ := μ) hx p q k k 0 (by omega) (by simpa using ho)) hi]
  congr 1
  rw [Polynomial.integralInner, integral_diskOuterMeasure_subtype μ hx _ ⟨_, ho⟩]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show k+k=2*k by omega, pow_mul,
    Real.sq_sqrt (diskCoordinates_sq_nonneg x)]
  ring

/-- An even gap between inner degrees transfers a polynomial radius power to the outer factor. -/
theorem integralInner_cartesianDiskPolynomial_of_degree_gap {μ ν : Measure ℝ}
    [SFinite μ] [SFinite ν] (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (p q u v : ℝ[X]) (k j r : ℕ) (hkj : k=j+2*r)
    (hu : u.natDegree ≤ k) (hv : v.natDegree ≤ j)
    (hpu : ∀ i, i % 2 ≠ k % 2 → u.coeff i = 0)
    (hpv : ∀ i, i % 2 ≠ j % 2 → v.coeff i = 0)
    (ho : Integrable (fun x => ((1-Polynomial.X^2)^r*p).eval x*q.eval x)
      (diskOuterMeasure j (μ.comap Subtype.val)) := by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hi : Integrable (fun z => u.eval z*v.eval z) ν := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (cartesianDiskPolynomial p u k) (cartesianDiskPolynomial q v j) (h := by
        exact integrable_cartesianDiskPolynomial_mul (μ := μ) (ν := ν)
          hx p q u v k j hu hv hpu hpv (integrable_disk_outer_factor (μ := μ) hx p q k j r hkj ho) hi)) =
      Polynomial.integralInner (diskOuterMeasure j (μ.comap Subtype.val)) (Polynomial.IntegrablePair.of (diskOuterMeasure j (μ.comap Subtype.val)) ((1-Polynomial.X^2)^r*p) q (h := by simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_X] using ho)) *
        Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν u v (h := hi)) := by
  rw [integralInner_cartesianDiskPolynomial hx p q u v k j hu hv hpu hpv
    (integrable_disk_outer_factor (μ := μ) hx p q k j r hkj ho) hi]
  congr 1
  rw [Polynomial.integralInner, integral_diskOuterMeasure_subtype μ hx _ ⟨_, ho⟩]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show k+j=2*(j+r) by omega, pow_mul,
    Real.sq_sqrt (diskCoordinates_sq_nonneg x)]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, pow_add]
  ring

end MvPolynomial
