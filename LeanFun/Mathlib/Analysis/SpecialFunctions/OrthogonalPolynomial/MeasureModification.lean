/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.PolynomialDensityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial modifications of one-dimensional orthogonality measures

Nonnegative nonzero polynomial densities preserve moments and strict positivity,
including modifications which vanish inside the support.
Reference: Gautschi, *Orthogonal Polynomials: Computation and Approximation*;
Gutleb–Olver–Slevinsky, polynomial measure modifications.
-/

public section
open MeasureTheory
open scoped NNReal ENNReal
namespace Polynomial
variable {μ : Measure ℝ}

/-- Integrability under a classical polynomial modification is weighted integrability. -/
theorem integrable_polynomialDensityMeasure_comap_iff (u : ℝ[X]) (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x) (f : ℝ → ℝ) :
    Integrable f (polynomialDensityMeasure u (μ.comap Subtype.val)) ↔
      Integrable (fun x => u.eval x * f x) μ := by
  obtain ⟨w, hw, hwval, _, he⟩ := exists_polynomialDensityMeasure_extension u
  rw [he, integrable_withDensity_iff_integrable_smul' hw.coe_nnreal_ennreal
    (Filter.Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  apply integrable_congr
  filter_upwards [hu] with x hx
  rw [hwval x hx]
  simp only [ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul]
/-- Integral transport for a bundled integrable input under a classical modification. -/
theorem integral_polynomialDensityMeasure_comap (u : ℝ[X]) (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x)
    (f : {f : ℝ → ℝ // Integrable f (polynomialDensityMeasure u (μ.comap Subtype.val))}) :
    ∫ x, f.val x ∂polynomialDensityMeasure u (μ.comap Subtype.val) =
      ∫ x, u.eval x * f.val x ∂μ := by
  rcases f with ⟨f, hf⟩
  change (∫ x, f x ∂polynomialDensityMeasure u (μ.comap Subtype.val)) =
    ∫ x, u.eval x * f x ∂μ
  obtain ⟨w, hw, hwval, _, he⟩ := exists_polynomialDensityMeasure_extension u
  rw [he, integral_withDensity_eq_integral_toReal_smul hw.coe_nnreal_ennreal
    (Filter.Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  rw [hwval x hx]
  simp only [ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul]

/-- A polynomial density on its nonnegative locus preserves finite moments. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.withDensity_polynomial {u : ℝ[X]} {μ : Measure {x : ℝ // 0 ≤ u.eval x}}
    (hμ : HasFiniteMoments (μ.map Subtype.val)) :
    HasFiniteMoments (polynomialDensityMeasure u μ) := by
  intro p
  erw [polynomialDensityMeasure, integrable_map_measure
    (p.continuous.pow 2).aestronglyMeasurable measurable_subtype_coe.aemeasurable]
  erw [integrable_withDensity_iff_integrable_smul
    (u.continuous.measurable.comp measurable_subtype_coe).nnreal_mk]
  have hi := (hμ.integrable_mul (u * p) p).comp_measurable measurable_subtype_coe
  convert hi using 1
  funext x
  simp only [Function.comp_apply, Pi.pow_apply, NNReal.smul_def, NNReal.coe_mk, smul_eq_mul, eval_mul]
  ring

theorem integrable_polynomialDensityMeasure_mul_iff {u : ℝ[X]} {μ : Measure {x : ℝ // 0 ≤ u.eval x}}
    (p q : ℝ[X]) :
    Integrable (fun x => p.eval x * q.eval x) (polynomialDensityMeasure u μ) ↔
      Integrable (fun x => (u * p).eval x * q.eval x) (μ.map Subtype.val) := by
  erw [polynomialDensityMeasure, integrable_map_measure
    (p.continuous.mul q.continuous).aestronglyMeasurable measurable_subtype_coe.aemeasurable,
    integrable_withDensity_iff_integrable_smul
      (u.continuous.measurable.comp measurable_subtype_coe).nnreal_mk,
    integrable_map_measure ((u * p).continuous.mul q.continuous).aestronglyMeasurable
      measurable_subtype_coe.aemeasurable]
  apply integrable_congr
  filter_upwards [] with x
  simp only [Function.comp_apply, Pi.mul_apply, NNReal.smul_def, NNReal.coe_mk,
    smul_eq_mul, eval_mul]
  ring

theorem integral_polynomialDensityMeasure_mul {u : ℝ[X]} {μ : Measure {x : ℝ // 0 ≤ u.eval x}}
    (p q : ℝ[X])
    (hi : Integrable (fun x => (u * p).eval x * q.eval x) (μ.map Subtype.val)) :
    ∫ x, p.eval x * q.eval x ∂polynomialDensityMeasure u μ =
      ∫ x, (u * p).eval x * q.eval x ∂μ.map Subtype.val := by
  have _hweighted := (integrable_polynomialDensityMeasure_mul_iff p q).mpr hi
  erw [polynomialDensityMeasure,
    integral_map measurable_subtype_coe.aemeasurable
      (p.continuous.mul q.continuous).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      ((u.continuous.measurable.comp measurable_subtype_coe).nnreal_mk.coe_nnreal_ennreal)
      (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top),
    integral_map measurable_subtype_coe.aemeasurable hi.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Function.comp_apply, Pi.mul_apply, ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul, eval_mul]
  ring

theorem integralInner_polynomialDensityMeasure {u : ℝ[X]} {μ : Measure {x : ℝ // 0 ≤ u.eval x}}
    (p q : ℝ[X]) (hi : Integrable (fun x => (u * p).eval x * q.eval x) (μ.map Subtype.val)) :
    integralInner (polynomialDensityMeasure u μ)
      (IntegrablePair.of (polynomialDensityMeasure u μ) p q ((integrable_polynomialDensityMeasure_mul_iff p q).mpr hi)) =
      integralInner (μ.map Subtype.val) (IntegrablePair.of (μ.map Subtype.val) (u * p) q hi) :=
  integral_polynomialDensityMeasure_mul p q hi

/-- A nonzero nonnegative polynomial density preserves a positive-definite pairing. -/
theorem HasPositiveDefiniteIntegral.withDensity_polynomial {u : ℝ[X]} {μ : Measure {x : ℝ // 0 ≤ u.eval x}}
    (hμ : HasFiniteMoments (μ.map Subtype.val))
    (hpos : HasPositiveDefiniteIntegral (μ.map Subtype.val)) (hu0 : u ≠ 0) :
    HasPositiveDefiniteIntegral (polynomialDensityMeasure u μ) := by
  refine ⟨HasFiniteMoments.withDensity_polynomial hμ, ?_⟩
  intro p hp
  simp only [pow_two]
  rw [integral_polynomialDensityMeasure_mul p p (hμ.integrable_mul (u * p) p)]
  have hi := hμ.integrable_mul (u * p) p
  have hn : 0 ≤ᵐ[μ.map Subtype.val] fun x => (u * p).eval x * p.eval x := by
    change ∀ᵐ x ∂μ.map Subtype.val, 0 ≤ (u * p).eval x * p.eval x
    erw [ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le measurable_const ((u * p).continuous.mul p.continuous).measurable)]
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Pi.mul_apply, eval_mul, mul_assoc, ← pow_two] using
        mul_nonneg x.property (sq_nonneg (p.eval (x : ℝ)))
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro heq
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp heq.symm
  have hup : integralInner (μ.map Subtype.val)
      (IntegrablePair.of (μ.map Subtype.val) (u * p) (u * p)) = 0 := by
    unfold integralInner
    calc
      _ = ∫ x, (0 : ℝ) ∂μ.map Subtype.val := integral_congr_ae (by
        filter_upwards [hz] with x hx
        simp only [Pi.zero_apply, eval_mul] at hx ⊢
        rcases mul_eq_zero.mp hx with h | h
        · rw [h, zero_mul]
        · simp [h])
      _ = 0 := integral_zero _ _
  exact (mul_ne_zero hu0 hp) (hpos.eq_zero_of_integralInner_self_eq_zero hup)

/-- Supported real sources transport to the classical polynomial density without losing mass. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem HasFiniteMoments.polynomialDensityMeasure {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (u : ℝ[X]) (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x) :
    HasFiniteMoments (Polynomial.polynomialDensityMeasure u (μ.comap Subtype.val)) := by
  apply HasFiniteMoments.withDensity_polynomial
  rwa [map_comap_polynomial_nonneg u μ hu]

/-- Strict positivity for the classical density of a supported real source. -/
theorem HasPositiveDefiniteIntegral.polynomialDensityMeasure {μ : Measure ℝ}
    (hpos : HasPositiveDefiniteIntegral μ) (hμ : HasFiniteMoments μ)
    (u : ℝ[X]) (hu0 : u ≠ 0) (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x) :
    HasPositiveDefiniteIntegral (Polynomial.polynomialDensityMeasure u (μ.comap Subtype.val)) := by
  apply HasPositiveDefiniteIntegral.withDensity_polynomial (u := u)
    (μ := μ.comap Subtype.val) _ _ hu0 <;>
    rwa [map_comap_polynomial_nonneg u μ hu]

/-- Integrability in a classical density measure on a supported real source. -/
theorem integrable_polynomialDensityMeasure_comap_mul_iff {μ : Measure ℝ}
    (u p q : ℝ[X]) (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x) :
    Integrable (fun x => p.eval x * q.eval x)
      (polynomialDensityMeasure u (μ.comap Subtype.val)) ↔
    Integrable (fun x => (u * p).eval x * q.eval x) μ := by
  rw [integrable_polynomialDensityMeasure_mul_iff, map_comap_polynomial_nonneg u μ hu]

/-- Polynomial pairings transport through the classical supported density. -/
theorem integralInner_polynomialDensityMeasure_comap {μ : Measure ℝ}
    (u p q : ℝ[X]) (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x)
    {hpq : Integrable (fun x => (u * p).eval x * q.eval x) μ} :
    integralInner (polynomialDensityMeasure u (μ.comap Subtype.val))
      (IntegrablePair.of _ p q ((integrable_polynomialDensityMeasure_comap_mul_iff u p q hu).2 hpq)) =
    integralInner μ (IntegrablePair.of μ (u * p) q hpq) := by
  have hi : Integrable (fun x => (u * p).eval x * q.eval x)
      ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  change (∫ x, p.eval x * q.eval x ∂polynomialDensityMeasure u (μ.comap Subtype.val)) =
    ∫ x, (u * p).eval x * q.eval x ∂μ
  simpa only [map_comap_polynomial_nonneg u μ hu] using
    integral_polynomialDensityMeasure_mul (μ := μ.comap Subtype.val) p q hi

end Polynomial
