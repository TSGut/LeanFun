/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.InnerProduct
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Algebra.Polynomial
public import LeanFun.Mathlib.MeasureTheory.Measure.NonnegativeDensity
public import LeanFun.Mathlib.MeasureTheory.Measure.EvenDensity

/-! # Polynomial density measures on their nonnegative domains

Reference: Gautschi, *Orthogonal Polynomials: Computation and Approximation*,
polynomial modifications of orthogonality measures.
-/

@[expose] public section
open MeasureTheory
open scoped NNReal ENNReal
namespace Polynomial

/-- Weight a measure on the nonnegative locus of a polynomial and return its real-coordinate measure. -/
noncomputable def polynomialDensityMeasure (p : ℝ[X])
    (μ : Measure {x : ℝ // 0 ≤ p.eval x}) : Measure ℝ :=
  Measure.map Subtype.val
    (μ.withDensity (fun x => ENNReal.ofNNReal (NNReal.mk (p.eval (x : ℝ)) x.property)))

/-- Evaluation on measurable sets is the nonnegative weighted source measure. -/
theorem polynomialDensityMeasure_apply (p : ℝ[X])
    (μ : Measure {x : ℝ // 0 ≤ p.eval x}) {s : Set ℝ} (hs : MeasurableSet s) :
    polynomialDensityMeasure p μ s =
      ∫⁻ x in Subtype.val ⁻¹' s, ENNReal.ofNNReal (NNReal.mk (p.eval (x : ℝ)) x.property) ∂μ := by
  rw [polynomialDensityMeasure, Measure.map_apply measurable_subtype_coe hs,
    withDensity_apply _ (measurable_subtype_coe hs)]

/-- Supported real measures transport without loss to a polynomial's nonnegative locus. -/
theorem map_comap_polynomial_nonneg (p : ℝ[X]) (μ : Measure ℝ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p.eval x) :
    Measure.map (Subtype.val : {x : ℝ // 0 ≤ p.eval x} → ℝ)
      (μ.comap Subtype.val) = μ := by
  have he := map_comap_subtype_coe (s := {x : ℝ | 0 ≤ p.eval x})
    (measurableSet_le measurable_const p.continuous.measurable) μ
  exact he.trans (Measure.restrict_eq_self_of_ae_mem hp)

/-- The constant unit density leaves the real source measure unchanged. -/
@[simp] theorem polynomialDensityMeasure_one_comap (μ : Measure ℝ) :
    polynomialDensityMeasure 1 (μ.comap Subtype.val) = μ := by
  convert map_comap_polynomial_nonneg (1 : ℝ[X]) μ (by simp) using 1
  simp [polynomialDensityMeasure]

/-- Successive nonnegative polynomial modifications multiply their densities.
The second factor is certified only for the first modified measure. -/
theorem withDensity_polynomial_mul (u v : ℝ[X])
    (μ : Measure {x : ℝ // 0 ≤ u.eval x})
    (hv : ∀ᵐ x ∂polynomialDensityMeasure u μ, 0 ≤ v.eval x) :
    polynomialDensityMeasure v ((polynomialDensityMeasure u μ).comap Subtype.val) =
      polynomialDensityMeasure (u * v) ((μ.map Subtype.val).comap Subtype.val) := by
  -- These zero extensions are proof devices; each polynomial is evaluated as a
  -- density only on its certified nonnegative locus.
  let w (p : ℝ[X]) (x : ℝ) : ℝ≥0 :=
    if h : 0 ≤ p.eval x then NNReal.mk (p.eval x) h else 0
  have hw (p : ℝ[X]) : Measurable (w p) := by
    apply measurable_coe_nnreal_real_iff.mp
    have he : (fun x => (w p x : ℝ)) =
        Set.piecewise {x | 0 ≤ p.eval x} (fun x => p.eval x) 0 := by
      funext x
      by_cases h : 0 ≤ p.eval x <;> simp [w, Set.piecewise, h]
    rw [he]
    exact p.continuous.measurable.piecewise
      (measurableSet_le measurable_const p.continuous.measurable) measurable_const
  have hmap (p : ℝ[X]) (η : Measure {x : ℝ // 0 ≤ p.eval x}) :
      polynomialDensityMeasure p η =
        (η.map Subtype.val).withDensity (fun x => (w p x : ℝ≥0∞)) := by
    ext s hs
    rw [polynomialDensityMeasure_apply p η hs, withDensity_apply _ hs,
      setLIntegral_map hs (hw p).coe_nnreal_ennreal measurable_subtype_coe]
    apply setLIntegral_congr_fun (measurable_subtype_coe hs)
    intro x _
    simp [w, x.property]
  have hcomap (p : ℝ[X]) (η : Measure ℝ) (hp : ∀ᵐ x ∂η, 0 ≤ p.eval x) :
      polynomialDensityMeasure p (η.comap Subtype.val) =
        η.withDensity (fun x => (w p x : ℝ≥0∞)) := by
    rw [hmap, map_comap_polynomial_nonneg p η hp]
  have hu : ∀ᵐ x ∂μ.map Subtype.val, 0 ≤ u.eval x := by
    rw [ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le measurable_const u.continuous.measurable)]
    exact Filter.Eventually.of_forall fun x => x.property
  have hv' : ∀ᵐ x ∂μ.map Subtype.val, (w u x : ℝ≥0∞) ≠ 0 → 0 ≤ v.eval x := by
    rw [hmap] at hv
    exact (ae_withDensity_iff (hw u).coe_nnreal_ennreal).mp hv
  have huv : ∀ᵐ x ∂μ.map Subtype.val, 0 ≤ (u * v).eval x := by
    filter_upwards [hu, hv'] with x hx hvx
    by_cases hz : u.eval x = 0
    · simp [eval_mul, hz]
    · rw [eval_mul]
      apply mul_nonneg hx (hvx ?_)
      simp only [w, dite_eq_left hx, ENNReal.coe_ne_zero]
      intro he
      exact hz (congrArg (fun a : ℝ≥0 => (a : ℝ)) he)
  rw [hcomap v _ hv, hmap, hcomap (u * v) _ huv,
    ← withDensity_mul _ (hw u).coe_nnreal_ennreal (hw v).coe_nnreal_ennreal]
  apply withDensity_congr_ae
  filter_upwards [hu, hv'] with x hx hvx
  by_cases hz : u.eval x = 0
  · simp [w, hz, eval_mul]
  · have hvx' : 0 ≤ v.eval x := hvx (by
      simp only [w, dite_eq_left hx, ENNReal.coe_ne_zero]
      intro he
      exact hz (congrArg (fun a : ℝ≥0 => (a : ℝ)) he))
    change (w u x : ℝ≥0∞) * (w v x : ℝ≥0∞) = (w (u * v) x : ℝ≥0∞)
    have hp : 0 ≤ (u * v).eval x := by simpa only [eval_mul] using mul_nonneg hx hvx'
    dsimp only [w]
    rw [dite_eq_left hx, dite_eq_left hvx', dite_eq_left hp, ← ENNReal.coe_mul]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, eval_mul]


/-- A measurable extension transports the classical density on its source locus. -/
theorem exists_polynomialDensityMeasure_extension (p : ℝ[X]) :
    ∃ w : ℝ → ℝ≥0, Measurable w ∧
      (∀ x (hx : 0 ≤ p.eval x), w x = NNReal.mk (p.eval x) hx) ∧
      (∀ x, ¬ 0 ≤ p.eval x → w x = 0) ∧
      ∀ μ : Measure ℝ, polynomialDensityMeasure p (μ.comap Subtype.val) =
        μ.withDensity (fun x => (w x : ℝ≥0∞)) :=
  exists_nonnegativeDensity_extension (fun x => p.eval x) p.continuous.measurable

/-- The classical supported density is absolutely continuous with respect to its source. -/
theorem polynomialDensityMeasure_comap_absolutelyContinuous (p : ℝ[X]) (μ : Measure ℝ) :
    polynomialDensityMeasure p (μ.comap Subtype.val) ≪ μ := by
  obtain ⟨w, _, _, _, he⟩ := exists_polynomialDensityMeasure_extension p
  rw [he]
  exact withDensity_absolutelyContinuous _ _

instance polynomialDensityMeasure_comap_sfinite (p : ℝ[X]) (μ : Measure ℝ) [SFinite μ] :
    SFinite (polynomialDensityMeasure p (μ.comap Subtype.val)) := by
  obtain ⟨w, _, _, _, he⟩ := exists_polynomialDensityMeasure_extension p
  rw [he]
  infer_instance

/-- Restricting to two nonnegative density loci and weighting commutes. -/
theorem polynomialDensityMeasure_comap_comm (p q : ℝ[X]) (μ : Measure ℝ) :
    polynomialDensityMeasure p ((polynomialDensityMeasure q (μ.comap Subtype.val)).comap Subtype.val) =
      polynomialDensityMeasure q ((polynomialDensityMeasure p (μ.comap Subtype.val)).comap Subtype.val) := by
  obtain ⟨w, hw, _, _, he⟩ := exists_polynomialDensityMeasure_extension p
  obtain ⟨v, hv, _, _, hf⟩ := exists_polynomialDensityMeasure_extension q
  rw [he, hf, hf, he, ← withDensity_mul μ hv.coe_nnreal_ennreal hw.coe_nnreal_ennreal,
    ← withDensity_mul μ hw.coe_nnreal_ennreal hv.coe_nnreal_ennreal, mul_comm]

/-- Reflection-invariant sources and even polynomial densities give even measures. -/
theorem isNegInvariant_polynomialDensityMeasure_comap (p : ℝ[X]) (μ : Measure ℝ)
    [μ.IsNegInvariant] (hp : ∀ x, p.eval (-x) = p.eval x) :
    (polynomialDensityMeasure p (μ.comap Subtype.val)).IsNegInvariant := by
  obtain ⟨w, _, hw, hz, he⟩ := exists_polynomialDensityMeasure_extension p
  rw [he]
  apply isNegInvariant_withDensity
  intro x
  congr 1
  by_cases hx : 0 ≤ p.eval x
  · rw [hw x hx, hw (-x) (by rwa [hp])]
    apply NNReal.eq
    exact hp x
  · rw [hz x hx, hz (-x) (by rwa [hp])]

end Polynomial
