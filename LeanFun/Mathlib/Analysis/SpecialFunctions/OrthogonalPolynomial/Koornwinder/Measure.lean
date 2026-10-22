/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Coordinates
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.SubtypeDensityMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.MeasureModification
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.InnerProduct
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# Measures for separated Koornwinder systems

The squared scale is a polynomial of unrestricted degree. Supports need not be
intervals. Reference: Dunkl–Xu, §2.6.1, generalized separated constructions.
-/

@[expose] public section
open MeasureTheory
namespace Polynomial

/-- An almost-everywhere squared-scale identity persists under a density change. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem ae_sq_eq_withDensity {D : Set ℝ} {μ : Measure D} {ρ : D → ℝ} {a : Polynomial ℝ}
    (f : D → ENNReal) (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ)) :
    ∀ᵐ x ∂μ.withDensity f, ρ x^2 = a.eval (x : ℝ) :=
  (withDensity_absolutelyContinuous _ _).ae_le ha


/-- A polynomial agreeing with a squared scale is nonnegative almost everywhere. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem ae_nonneg_eval_of_sq_eq {D : Set ℝ} {μ : Measure D} {ρ : D → ℝ} {a : ℝ[X]}
    (ha : ∀ᵐ x ∂μ, ρ x^2 = a.eval (x : ℝ)) : ∀ᵐ (x : D) ∂μ, 0 ≤ a.eval (x : ℝ) :=
  ha.mono (fun x hx => hx ▸ sq_nonneg (ρ x))

/-- The degree-k measure lives on the nonnegative locus of the degree-k density. -/
noncomputable def koornwinderOuterMeasure (a : ℝ[X]) (k : ℕ)
    (μ : Measure {x : ℝ // 0 ≤ (a^k).eval x}) : Measure ℝ :=
  polynomialDensityMeasure (a^k) μ

/-- The shifted measure is characterized by its nonnegative source integral. -/
theorem koornwinderOuterMeasure_apply (a : ℝ[X]) (k : ℕ)
    (μ : Measure {x : ℝ // 0 ≤ (a^k).eval x}) {s : Set ℝ} (hs : MeasurableSet s) :
    koornwinderOuterMeasure a k μ s =
      ∫⁻ x in Subtype.val ⁻¹' s,
        ENNReal.ofNNReal (NNReal.mk ((a^k).eval (x : ℝ)) x.property) ∂μ :=
  polynomialDensityMeasure_apply (a^k) μ hs

/-- Degree zero leaves the original real measure unchanged. -/
@[simp] theorem koornwinderOuterMeasure_zero (a : ℝ[X]) (μ : Measure ℝ) :
    koornwinderOuterMeasure a 0 (μ.comap Subtype.val) = μ := by
  simp only [koornwinderOuterMeasure]
  exact polynomialDensityMeasure_one_comap μ

/-- Integrals in a shifted outer measure, for a bundled integrable input. -/
theorem integral_koornwinderOuterMeasure (μ : Measure ℝ) (a : ℝ[X])
    (ha : ∀ᵐ x ∂μ, 0 ≤ a.eval x) (k : ℕ)
    (f : {f : ℝ → ℝ // Integrable f (koornwinderOuterMeasure a k (μ.comap Subtype.val))}) :
    ∫ x, f.val x ∂koornwinderOuterMeasure a k (μ.comap Subtype.val) =
      ∫ x, (a.eval x)^k*f.val x ∂μ := by
  rcases f with ⟨f,hf⟩
  change (∫ x, f x ∂polynomialDensityMeasure (a^k) (μ.comap Subtype.val)) =
    ∫ x, (a.eval x)^k*f x ∂μ
  have hu : ∀ᵐ x ∂μ, 0 ≤ (a^k).eval x := by
    filter_upwards [ha] with x hx
    simpa only [eval_pow] using pow_nonneg hx k
  simpa only [eval_pow] using integral_polynomialDensityMeasure_comap (a^k) hu ⟨f,hf⟩

/-- Every shifted outer measure has finite moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.koornwinderOuterMeasure {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (a : ℝ[X]) (ha : ∀ᵐ x ∂μ, 0 ≤ a.eval x) (k : ℕ) :
    HasFiniteMoments (koornwinderOuterMeasure a k (μ.comap Subtype.val)) := by
  apply hμ.polynomialDensityMeasure (a^k)
  filter_upwards [ha] with x hx
  simpa only [eval_pow] using pow_nonneg hx k

/-- Nonzero squared scales preserve strict positivity of the shifted pairings. -/
theorem HasPositiveDefiniteIntegral.koornwinderOuterMeasure {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (a : ℝ[X]) (ha0 : a ≠ 0) (ha : ∀ᵐ x ∂μ, 0 ≤ a.eval x) (k : ℕ) :
    HasPositiveDefiniteIntegral (koornwinderOuterMeasure a k (μ.comap Subtype.val)) := by
  apply hpos.polynomialDensityMeasure hμ (a^k) (pow_ne_zero _ ha0)
  filter_upwards [ha] with x hx
  simpa only [eval_pow] using pow_nonneg hx k

/-- Nonnegativity on the domain transfers to its real coordinate measure. -/
theorem ae_nonneg_eval_map_subtype {D : Set ℝ} {μ : Measure D} {p : ℝ[X]}
    (hp : ∀ᵐ x : D ∂μ, 0 ≤ p.eval (x : ℝ)) :
    ∀ᵐ x ∂Measure.map Subtype.val μ, 0 ≤ p.eval x :=
  (ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_le measurable_const p.continuous.measurable)).mpr hp

/-- Finite moments survive a polynomial density on an outer domain. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.map_subtype_withDensity {D : Set ℝ} {μ : Measure D}
    (hμ : HasFiniteMoments (Measure.map Subtype.val μ)) (p : ℝ[X])
    (hp : ∀ᵐ x : D ∂μ, 0 ≤ p.eval (x : ℝ)) :
    HasFiniteMoments (Measure.map Subtype.val
      (subtypeDensityMeasure p (μ.comap Subtype.val))) := by
  rw [map_subtypeDensityMeasure_comap]
  exact hμ.polynomialDensityMeasure p (ae_nonneg_eval_map_subtype hp)

/-- Positive polynomial pairings survive a nonzero nonnegative density on the domain. -/
theorem HasPositiveDefiniteIntegral.map_subtype_withDensity {D : Set ℝ} {μ : Measure D}
    (hpos : HasPositiveDefiniteIntegral (Measure.map Subtype.val μ))
    (hμ : HasFiniteMoments (Measure.map Subtype.val μ)) (p : ℝ[X]) (hp0 : p ≠ 0)
    (hp : ∀ᵐ x : D ∂μ, 0 ≤ p.eval (x : ℝ)) :
    HasPositiveDefiniteIntegral (Measure.map Subtype.val
      (subtypeDensityMeasure p (μ.comap Subtype.val))) := by
  rw [map_subtypeDensityMeasure_comap]
  exact hpos.polynomialDensityMeasure hμ p hp0 (ae_nonneg_eval_map_subtype hp)

/-- Integrable shifted inputs transport to their outer domain. -/
theorem integral_koornwinderOuterMeasure_map_subtype {D : Set ℝ}
    (μ : Measure D) (a : ℝ[X]) (ha : ∀ᵐ x : D ∂μ, 0 ≤ a.eval (x : ℝ)) (k : ℕ)
    (f : {f : ℝ → ℝ // Integrable f
      (koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val))}) :
    ∫ x, f.val x ∂koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val) =
      ∫ x : D, a.eval (x : ℝ)^k*f.val x ∂μ := by
  rcases f with ⟨f,hf⟩
  change (∫ x, f x ∂koornwinderOuterMeasure a k ((Measure.map Subtype.val μ).comap Subtype.val)) =
    ∫ x : D, a.eval (x : ℝ)^k*f x ∂μ
  have hu : ∀ᵐ x ∂Measure.map Subtype.val μ, 0 ≤ (a^k).eval x := by
    filter_upwards [ae_nonneg_eval_map_subtype ha] with x hx
    simpa only [eval_pow] using pow_nonneg hx k
  have hw := (integrable_polynomialDensityMeasure_comap_iff (a^k) hu f).mp hf
  calc
    _ = ∫ x, a.eval x^k*f x ∂Measure.map Subtype.val μ :=
      integral_koornwinderOuterMeasure _ a (ae_nonneg_eval_map_subtype ha) k ⟨f,hf⟩
    _ = _ := integral_map measurable_subtype_coe.aemeasurable
      (by simpa only [eval_pow] using hw.aestronglyMeasurable)

/-- Moments of the real coordinate imply finite mass on the outer domain. -/
theorem HasFiniteMoments.isFiniteMeasure_subtype {D : Set ℝ} {μ : Measure D}
    (hμ : HasFiniteMoments (Measure.map Subtype.val μ)) : IsFiniteMeasure μ := by
  let := hμ.isFiniteMeasure
  exact Measure.isFiniteMeasure_of_map measurable_subtype_coe.aemeasurable

end Polynomial
namespace MvPolynomial
variable {D : Set ℝ}

/-- Separated coordinates with an arbitrary continuous scale. -/
def koornwinderCoordinates (ρ : D → ℝ) (v : D × ℝ) : Fin 2 → ℝ := ![(v.1 : ℝ), ρ v.1*v.2]

/-- The separated coordinate map is continuous when its scale is. -/
theorem continuous_koornwinderCoordinates {ρ : D → ℝ} (hρ : Continuous ρ) :
    Continuous (koornwinderCoordinates ρ) := by
  unfold koornwinderCoordinates
  fun_prop

/-- Certificates for the product kernel and the separated coordinate pushforward. -/
structure KoornwinderMeasureInput (ρ : D → ℝ) (μ : Measure D) (ν : Measure ℝ) : Prop where
  product_measurable : AEMeasurable (fun x : D ↦ Measure.map (Prod.mk x) ν) μ
  coordinates_measurable : AEMeasurable (koornwinderCoordinates ρ) (μ.prod ν)

/-- Continuous scales and s-finite inner factors supply both certificates. -/
theorem KoornwinderMeasureInput.ofContinuous {ρ : D → ℝ} (μ : Measure D) (ν : Measure ℝ)
    [SFinite ν] (hρ : Continuous ρ) : KoornwinderMeasureInput ρ μ ν :=
  ⟨Measurable.map_prodMk_left.aemeasurable,
    (continuous_koornwinderCoordinates hρ).measurable.aemeasurable⟩

/-- Finite polynomial moments also supply the inner product-kernel certificate. -/
theorem KoornwinderMeasureInput.ofMoments {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ}
    (hν : Polynomial.HasFiniteMoments ν) (hρ : Continuous ρ) :
    KoornwinderMeasureInput ρ μ ν := by
  let := hν.isFiniteMeasure
  exact KoornwinderMeasureInput.ofContinuous μ ν hρ

/-- Transport certified product measures through certified separated coordinates. -/
noncomputable def koornwinderMeasure (ρ : D → ℝ) (μ : Measure D) (ν : Measure ℝ)
    (input : KoornwinderMeasureInput ρ μ ν := by
      first
        | assumption
        | exact KoornwinderMeasureInput.ofContinuous _ _ (by fun_prop)
        | (apply KoornwinderMeasureInput.ofMoments
           · aesop (rule_sets := [PolynomialIntegrability])
           · fun_prop)) :
    Measure (Fin 2 → ℝ) :=
  let certified : ProductMeasureInput (β := ℝ) μ := ⟨ν, input.product_measurable⟩
  Measure.map (koornwinderCoordinates ρ) (μ.prod certified.inner)

/-- Certified separated pushforward on measurable sets. -/
theorem koornwinderMeasure_apply {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ}
    (input : KoornwinderMeasureInput ρ μ ν) {s : Set (Fin 2 → ℝ)}
    (hs : MeasurableSet s) :
    koornwinderMeasure ρ μ ν input s = (μ.prod ν) ((koornwinderCoordinates ρ) ⁻¹' s) :=
  Measure.map_apply_of_aemeasurable input.coordinates_measurable hs

/-- Integrable inputs have integrable pullbacks and the same integral. -/
theorem koornwinderMeasure_integral {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ}
    (input : KoornwinderMeasureInput ρ μ ν)
    (f : IntegrableInput (koornwinderMeasure ρ μ ν input)) :
    Integrable (fun v ↦ f.val (koornwinderCoordinates ρ v)) (μ.prod ν) ∧
    (∫ v, f.val v ∂koornwinderMeasure ρ μ ν input) =
      ∫ v, f.val (koornwinderCoordinates ρ v) ∂μ.prod ν := by
  constructor
  · exact (integrable_map_measure f.integrable.aestronglyMeasurable
      input.coordinates_measurable).mp f.integrable
  · exact integral_map input.coordinates_measurable f.integrable.aestronglyMeasurable




/-- Integrable real-coordinate pullbacks on the full outer domain. -/
theorem koornwinderMeasure_integral_univ (r : ℝ → ℝ) (hr : Continuous r)
    (μ ν : Measure ℝ) [SFinite ν]
    (f : IntegrableInput (koornwinderMeasure (fun x : (Set.univ : Set ℝ) ↦ r (x : ℝ))
      (Measure.comap Subtype.val μ) ν
      (KoornwinderMeasureInput.ofContinuous _ ν (hr.comp continuous_subtype_val)))) :
    Integrable (fun v : ℝ × ℝ ↦ f.val (![v.1,r v.1*v.2])) (μ.prod ν) ∧
    (∫ v, f.val v ∂koornwinderMeasure (fun x : (Set.univ : Set ℝ) ↦ r (x : ℝ))
      (Measure.comap Subtype.val μ) ν
      (KoornwinderMeasureInput.ofContinuous _ ν (hr.comp continuous_subtype_val))) =
      ∫ v : ℝ × ℝ, f.val (![v.1,r v.1*v.2]) ∂μ.prod ν := by
  let e := (MeasurableEquiv.Set.univ ℝ).prodCongr (MeasurableEquiv.refl ℝ)
  have he : Measure.map e ((Measure.comap (Subtype.val : ↥(Set.univ : Set ℝ) → ℝ) μ).prod ν) = μ.prod ν := by
    change Measure.map (Prod.map Subtype.val id) _ = _
    rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
      map_comap_subtype_coe MeasurableSet.univ, Measure.restrict_univ, Measure.map_id]
  have hc := koornwinderMeasure_integral
    (KoornwinderMeasureInput.ofContinuous _ ν (hr.comp continuous_subtype_val)) f
  have hi : Integrable (fun v : ℝ × ℝ ↦ f.val (![v.1,r v.1*v.2])) (μ.prod ν) := by
    rw [← he, e.measurableEmbedding.integrable_map_iff]
    exact hc.1
  refine ⟨hi, hc.2.trans ?_⟩
  rw [← he, integral_map_equiv]
  rfl
end MvPolynomial
