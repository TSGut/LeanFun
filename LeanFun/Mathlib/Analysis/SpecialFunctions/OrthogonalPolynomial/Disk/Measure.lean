/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.PolynomialDensityMeasure
public import Mathlib.Topology.Algebra.Polynomial

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.CompactMoments
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Moments

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Polynomial
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.MeasureModification
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.InnerProduct
public import LeanFun.Mathlib.MeasureTheory.Measure.EvenDensity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Measures for general Cartesian disk systems

The inner degree k shifts the outer measure by (1-x²)^k. This layer keeps
both original one-dimensional measures arbitrary and allows polynomial density
modifications with interior zeros.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

@[expose] public section
open MeasureTheory Set
namespace Polynomial

/-- The separated outer factors are integrable on the compact outer support. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.integrable_disk_outer_factor {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (_hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (p q : ℝ[X]) (r : ℕ) :
    Integrable (fun x : Icc (-1 : ℝ) 1 =>
      p.eval (x : ℝ)*q.eval (x : ℝ)*Real.sqrt (1-(x : ℝ)^2)^r)
      (μ.comap Subtype.val) := by
  let := hμ.isFiniteMeasure
  have hc : Continuous (fun x : Icc (-1 : ℝ) 1 =>
      p.eval (x : ℝ)*q.eval (x : ℝ)*Real.sqrt (1-(x : ℝ)^2)^r) := by fun_prop
  simpa only [integrableOn_univ] using
    hc.continuousOn.integrableOn_compact (μ := μ.comap Subtype.val) isCompact_univ

/-- The outer density is defined on its full nonnegative locus at degree k. -/
noncomputable def diskOuterMeasure (k : ℕ)
    (μ : Measure {x : ℝ // 0 ≤ ((1-X^2 : ℝ[X])^k).eval x}) : Measure ℝ :=
  polynomialDensityMeasure ((1-X^2)^k) μ

/-- The density at degree zero leaves the source unchanged. -/
@[simp] theorem diskOuterMeasure_zero (μ : Measure ℝ) :
    diskOuterMeasure 0 (μ.comap Subtype.val) = μ := by
  simp only [diskOuterMeasure]
  exact polynomialDensityMeasure_one_comap μ

/-- Values on measurable sets are the nonnegative weighted source integrals. -/
theorem diskOuterMeasure_apply (k : ℕ)
    (μ : Measure {x : ℝ // 0 ≤ ((1-X^2 : ℝ[X])^k).eval x})
    {s : Set ℝ} (hs : MeasurableSet s) :
    diskOuterMeasure k μ s = ∫⁻ x in Subtype.val ⁻¹' s,
      ENNReal.ofNNReal (NNReal.mk (((1-X^2 : ℝ[X])^k).eval (x : ℝ)) x.property) ∂μ :=
  polynomialDensityMeasure_apply _ μ hs

/-- The outer-measure integral, for a bundled integrable input. -/
theorem integral_diskOuterMeasure (μ : Measure ℝ)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (k : ℕ)
    (f : {f : ℝ → ℝ // Integrable f (diskOuterMeasure k (μ.comap Subtype.val))}) :
    ∫ x, f.val x ∂diskOuterMeasure k (μ.comap Subtype.val) =
      ∫ x, (1-x^2)^k * f.val x ∂μ := by
  rcases f with ⟨f, hf⟩
  change (∫ x, f x ∂polynomialDensityMeasure ((1-X^2)^k) (μ.comap Subtype.val)) =
    ∫ x, (1-x^2)^k*f x ∂μ
  have hu : ∀ᵐ x ∂μ, 0 ≤ ((1-X^2 : ℝ[X])^k).eval x := by
    filter_upwards [hx] with x hx
    simp only [eval_pow, eval_sub, eval_one, eval_X]
    exact pow_nonneg (by nlinarith [hx.1,hx.2]) k
  simpa only [eval_pow, eval_sub, eval_one, eval_X] using
    integral_polynomialDensityMeasure_comap ((1-X^2)^k) hu ⟨f,hf⟩

/-- Classical outer transport retains the closed interval, including its endpoints. -/
theorem integral_diskOuterMeasure_subtype (μ : Measure ℝ)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (k : ℕ)
    (f : {f : ℝ → ℝ // Integrable f (diskOuterMeasure k (μ.comap Subtype.val))}) :
    ∫ x, f.val x ∂diskOuterMeasure k (μ.comap Subtype.val) =
      ∫ x : Icc (-1 : ℝ) 1, (1-(x : ℝ)^2)^k * f.val x ∂μ.comap Subtype.val := by
  rcases f with ⟨f, hf⟩
  change (∫ x, f x ∂diskOuterMeasure k (μ.comap Subtype.val)) =
    ∫ x : Icc (-1 : ℝ) 1, (1-(x : ℝ)^2)^k * f x ∂μ.comap Subtype.val
  have hu : ∀ᵐ x ∂μ, 0 ≤ ((1-X^2 : ℝ[X])^k).eval x := by
    filter_upwards [hx] with x hx
    simp only [eval_pow, eval_sub, eval_one, eval_X]
    exact pow_nonneg (by nlinarith [hx.1, hx.2]) k
  have hw := (integrable_polynomialDensityMeasure_comap_iff ((1-X^2)^k) hu f).mp hf
  have hm : Measure.map (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
      (μ.comap Subtype.val) = μ := by
    rw [map_comap_subtype_coe measurableSet_Icc, Measure.restrict_eq_self_of_ae_mem hx]
  have hwm : AEStronglyMeasurable (fun x => ((1-X^2 : ℝ[X])^k).eval x*f x)
      (Measure.map (Subtype.val : Icc (-1 : ℝ) 1 → ℝ) (μ.comap Subtype.val)) := by
    simpa only [hm] using hw.aestronglyMeasurable
  calc
    _ = ∫ x, ((1-X^2 : ℝ[X])^k).eval x*f x ∂μ :=
      integral_polynomialDensityMeasure_comap _ hu ⟨f,hf⟩
    _ = ∫ x : Icc (-1 : ℝ) 1, ((1-X^2 : ℝ[X])^k).eval (x : ℝ)*f x
        ∂μ.comap Subtype.val := by
      simpa only [hm] using integral_map measurable_subtype_coe.aemeasurable hwm
    _ = _ := by simp only [eval_pow, eval_sub, eval_one, eval_X]

/-- The shifted outer measure still has every polynomial moment. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.diskOuterMeasure {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (k : ℕ) :
    HasFiniteMoments (diskOuterMeasure k (μ.comap Subtype.val)) := by
  have hu : ∀ᵐ x ∂μ, 0 ≤ ((1-X^2 : ℝ[X])^k).eval x := by
    filter_upwards [hx] with x hx
    simp only [eval_pow, eval_sub, eval_one, eval_X]
    exact pow_nonneg (by nlinarith [hx.1,hx.2]) _
  exact hμ.polynomialDensityMeasure ((1-X^2)^k) hu

/-- Continuous functions are integrable for a shifted finite interval measure. -/
theorem integrable_diskOuterMeasure_of_continuous {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (k : ℕ) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f (diskOuterMeasure k (μ.comap Subtype.val)) := by
  let := ((hasFiniteMoments_of_ae_mem_Icc hx).diskOuterMeasure hx k).isFiniteMeasure
  have hs : ∀ᵐ x ∂diskOuterMeasure k (μ.comap Subtype.val), x ∈ Icc (-1 : ℝ) 1 :=
    (polynomialDensityMeasure_comap_absolutelyContinuous ((1-X^2)^k) μ).ae_le hx
  have hi := hf.integrableOn_Icc (μ := diskOuterMeasure k (μ.comap Subtype.val))
    (a := (-1 : ℝ)) (b := 1)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at hi

/-- Strict positivity is preserved by the outer degree shift. -/
theorem HasPositiveDefiniteIntegral.diskOuterMeasure {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (k : ℕ) :
    HasPositiveDefiniteIntegral (diskOuterMeasure k (μ.comap Subtype.val)) := by
  have hu0 : (1-X^2 : ℝ[X])^k ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] => p.eval 0) h
    simp at he
  have hu : ∀ᵐ x ∂μ, 0 ≤ ((1-X^2 : ℝ[X])^k).eval x := by
    filter_upwards [hx] with x hx
    simp only [eval_pow, eval_sub, eval_one, eval_X]
    exact pow_nonneg (by nlinarith [hx.1,hx.2]) _
  exact hpos.polynomialDensityMeasure hμ ((1-X^2)^k) hu0 hu

/-- An even outer measure remains even after a degree shift. -/
theorem isNegInvariant_diskOuterMeasure (μ : Measure ℝ) [μ.IsNegInvariant] (k : ℕ) :
    (diskOuterMeasure k (μ.comap Subtype.val)).IsNegInvariant := by
  apply isNegInvariant_polynomialDensityMeasure_comap
  intro x
  simp

end Polynomial
namespace MvPolynomial

instance isFiniteMeasure_cartesianDiskMeasure (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) := by
  unfold cartesianDiskMeasure
  infer_instance

/-- Continuous functions are integrable for Cartesian images of compactly supported factors. -/
theorem integrable_cartesianDiskMeasure {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (_hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)
    {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) := by
  change Integrable f (Measure.map diskCoordinates
    ((Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ) μ).prod ν))
  rw [integrable_map_measure hf.aestronglyMeasurable
    continuous_diskCoordinates.measurable.aemeasurable]
  have hi := (hf.comp continuous_diskCoordinates).continuousOn.integrableOn_compact
    (μ := (Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ) μ).prod ν)
    (isCompact_univ.prod isCompact_Icc :
      IsCompact (univ ×ˢ Icc (-1 : ℝ) 1 : Set (Icc (-1 : ℝ) 1 × ℝ)))
  have ha : ∀ᵐ v ∂(Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ) μ).prod ν,
      v ∈ (univ ×ˢ Icc (-1 : ℝ) 1 : Set (Icc (-1 : ℝ) 1 × ℝ)) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hz] with v hv
    exact ⟨mem_univ _, hv⟩
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi

/-- Continuous Cartesian integrals separate on the typed outer interval. -/
theorem integral_cartesianDiskMeasure_eq_iterated {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)
    {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    ∫ v, f v ∂cartesianDiskMeasure (μ.comap Subtype.val)
        (ProductMeasureInput.ofSFinite (μ.comap Subtype.val) ν) =
      ∫ x : Icc (-1 : ℝ) 1, ∫ z, f (diskCoordinates (x,z)) ∂ν ∂μ.comap Subtype.val := by
  have hi := (cartesianDiskMeasure_integral (μ.comap Subtype.val)
    (ProductMeasureInput.ofSFinite (μ.comap Subtype.val) ν)
    ⟨f, integrable_cartesianDiskMeasure hx hz hf⟩).1
  rw [(cartesianDiskMeasure_integral (μ.comap Subtype.val)
    (ProductMeasureInput.ofSFinite (μ.comap Subtype.val) ν)
    ⟨f, integrable_cartesianDiskMeasure hx hz hf⟩).2]
  exact integral_prod _ hi

/-- Outer interval support and moments of both factors suffice for Cartesian moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_cartesianDiskMeasure_of_moments {μ ν : Measure ℝ}
    (hμ : Polynomial.HasFiniteMoments μ) (hν : Polynomial.HasFiniteMoments ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) :
    HasFiniteMoments (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (hν := by let := hν.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) := by
  let := hν.isFiniteMeasure
  have hm : Polynomial.HasFiniteMoments
      (Measure.map Subtype.val (Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ) μ)) := by
    simpa only [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem hx] using hμ
  have ha : ∀ᵐ x : Icc (-1 : ℝ) 1 ∂Measure.comap Subtype.val μ,
      Real.sqrt (1-(x : ℝ)^2)^2 = (1-Polynomial.X^2 : Polynomial ℝ).eval (x : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X] using Real.sq_sqrt (diskCoordinates_sq_nonneg x)
  exact
    hasFiniteMoments_koornwinderMeasure
      (ρ := fun x : Icc (-1 : ℝ) 1 => Real.sqrt (1-(x : ℝ)^2)) hm hν
      (by fun_prop) (1-Polynomial.X^2) ha

/-- Cartesian disk measures have all polynomial moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_cartesianDiskMeasure {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1) :
    HasFiniteMoments (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) := by
  intro p
  exact integrable_cartesianDiskMeasure hx hz (p.continuous_eval.pow 2)

end MvPolynomial
