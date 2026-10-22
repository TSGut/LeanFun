/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Measure
public import LeanFun.Mathlib.Algebra.MvPolynomial.ScaledLift
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Actual polynomial densities for separated modifications

The lifted density descends from product coordinates to a bivariate polynomial.
The integral identity requires no compact-support assumption.
Reference: Dunkl–Xu, §2.6.1; Gutleb–Olver–Slevinsky, polynomial modification.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace MvPolynomial
variable {D : Set ℝ}

/-- A separated modification as a genuine bivariate polynomial. -/
noncomputable def koornwinderModificationPolynomial (b h g : ℝ[X]) (step : ℕ+) (l : ℕ) :
    MvPolynomial (Fin 2) ℝ := h.eval₂ C (X 0) * scaledLift b step ((step : ℕ)*l) g

/-- Evaluation of the modification in separated coordinates. -/
theorem eval_koornwinderModificationPolynomial (b h g : ℝ[X]) (step : ℕ+) (l : ℕ)
    (hg : g.natDegree ≤ (step : ℕ)*l)
    (hpar : ∀ j ≤ (step : ℕ)*l, g.coeff j ≠ 0 → (step : ℕ) ∣ (step : ℕ)*l-j)
    (ρ : D → ℝ) (x : D) (z : ℝ) (hb : ρ x^(step : ℕ) = b.eval (x : ℝ)) :
    eval (koornwinderCoordinates ρ (x,z)) (koornwinderModificationPolynomial b h g step l) =
      (b^l*h).eval (x : ℝ) * g.eval z := by
  rw [koornwinderModificationPolynomial, map_mul, eval_eval₂_C_X,
    eval_scaledLift b step ((step : ℕ)*l) g hg hpar _ (ρ x) z
      (by simpa [koornwinderCoordinates] using hb.symm) rfl,
    pow_mul, hb]
  simp only [koornwinderCoordinates, Matrix.cons_val_zero, Polynomial.eval_mul, Polynomial.eval_pow]
  ring

/-- Degree-compatible scale powers bound the physical density's total degree. -/
theorem totalDegree_koornwinderModificationPolynomial_le (b h g : ℝ[X]) (step : ℕ+) (l : ℕ)
    (hb : b.natDegree ≤ (step : ℕ)) :
    (koornwinderModificationPolynomial b h g step l).totalDegree ≤ h.natDegree+(step : ℕ)*l :=
  (totalDegree_mul _ _).trans (Nat.add_le_add (totalDegree_eval₂_C_X_le h 0)
    (totalDegree_scaledLift_le b step ((step : ℕ)*l) g hb))

/-- The former zero-step modification is an ordinary constant vertical factor.
This statement uses coefficient truncation, with no division by a scale step. -/
theorem eval_zeroStepKoornwinderModification (b h g : ℝ[X]) (l : ℕ)
    (hg : g.natDegree ≤ 0) (v : Fin 2 → ℝ) (z : ℝ) (hb : b.eval (v 0) = 1) :
    eval v (h.eval₂ C (X 0) * verticalTruncation 0 g) =
      (b^l*h).eval (v 0) * g.eval z := by
  have hgval : g.eval z = g.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range' (by omega : g.natDegree < 0+1)]
    simp
  simp [verticalTruncation, eval_eval₂_C_X, hgval, hb]

/-- The zero-step product construction has degree bounded by the outer factor. -/
theorem totalDegree_zeroStepKoornwinderModification_le (h g : ℝ[X]) :
    (h.eval₂ C (X 0) * verticalTruncation 0 g).totalDegree ≤ h.natDegree := by
  simpa using (totalDegree_mul _ _).trans
    (Nat.add_le_add (totalDegree_eval₂_C_X_le h (0 : Fin 2))
      (totalDegree_verticalTruncation_le 0 g))

/-- Integrability is transported by the descended polynomial density. -/
theorem integrable_eval_koornwinder_modification_iff {μ : Measure D} {ν : Measure ℝ}
    [SFinite ν] {ρ : D → ℝ} (hρ : Continuous ρ)
    (h g : ℝ[X]) (hh : ∀ᵐ (x : D) ∂μ, 0 ≤ h.eval (x : ℝ)) (hg : ∀ᵐ z ∂ν, 0 ≤ g.eval z)
    (u p : MvPolynomial (Fin 2) ℝ)
    (hu : ∀ᵐ (x : D) ∂μ, ∀ z, eval (koornwinderCoordinates ρ (x,z)) u = h.eval (x : ℝ)*g.eval z) :
    Integrable (fun v => eval v p) (koornwinderMeasure ρ
      (Polynomial.subtypeDensityMeasure (h) ((μ).comap Subtype.val))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val))) ↔
      Integrable (fun v => eval v (u*p)) (koornwinderMeasure ρ μ ν) := by
  obtain ⟨w, hw, hwval, _, hwmeasure⟩ := exists_subtypeDensityMeasure_extension h (D := D)
  obtain ⟨v, hv, hvval, _, hvmeasure⟩ := exists_polynomialDensityMeasure_extension g
  rw [koornwinderMeasure, koornwinderMeasure,
    integrable_map_measure p.continuous_eval.aestronglyMeasurable
      (continuous_koornwinderCoordinates hρ).measurable.aemeasurable,
    integrable_map_measure (u*p).continuous_eval.aestronglyMeasurable
      (continuous_koornwinderCoordinates hρ).measurable.aemeasurable]
  change Integrable ((fun x => eval x p) ∘ koornwinderCoordinates ρ)
      ((subtypeDensityMeasure h (μ.comap Subtype.val)).prod
        (polynomialDensityMeasure g (ν.comap Subtype.val))) ↔
    Integrable ((fun x => eval x (u*p)) ∘ koornwinderCoordinates ρ) (μ.prod ν)
  rw [hwmeasure, hvmeasure,
    prod_withDensity hw.coe_nnreal_ennreal hv.coe_nnreal_ennreal]
  erw [integrable_withDensity_iff_integrable_smul'
      ((hw.comp measurable_fst).coe_nnreal_ennreal.mul
        (hv.comp measurable_snd).coe_nnreal_ennreal)
      (Filter.Eventually.of_forall (fun _ => ENNReal.mul_lt_top
        ENNReal.coe_lt_top ENNReal.coe_lt_top))]
  apply integrable_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hh,
    Measure.quasiMeasurePreserving_snd.ae hg, Measure.quasiMeasurePreserving_fst.ae hu]
    with x hx hz hux
  simp only [Function.comp_apply, Pi.mul_apply, ENNReal.toReal_mul, hwval x.1 hx, hvval x.2 hz,
    ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul, map_mul, hux x.2]

/-- Product-factor density changes transport classically integrable polynomial inputs. -/
theorem integral_eval_koornwinder_modification {μ : Measure D} {ν : Measure ℝ}
    [SFinite ν] {ρ : D → ℝ} (hρ : Continuous ρ)
    (h g : ℝ[X]) (hh : ∀ᵐ (x : D) ∂μ, 0 ≤ h.eval (x : ℝ)) (hg : ∀ᵐ z ∂ν, 0 ≤ g.eval z)
    (u : MvPolynomial (Fin 2) ℝ)
    (p : {p : MvPolynomial (Fin 2) ℝ //
      Integrable (fun v => eval v (u*p)) (koornwinderMeasure ρ μ ν)})
    (hu : ∀ᵐ (x : D) ∂μ, ∀ z, eval (koornwinderCoordinates ρ (x,z)) u = h.eval (x : ℝ)*g.eval z) :
    ∫ v, eval v p.val ∂koornwinderMeasure ρ
      (Polynomial.subtypeDensityMeasure h (μ.comap Subtype.val))
      (Polynomial.polynomialDensityMeasure g (ν.comap Subtype.val)) =
      ∫ v, eval v (u*p.val) ∂koornwinderMeasure ρ μ ν := by
  have hi := (integrable_eval_koornwinder_modification_iff hρ h g hh hg u p.val hu).2
    p.property
  obtain ⟨w, hw, hwval, _, hwmeasure⟩ := exists_subtypeDensityMeasure_extension h (D := D)
  obtain ⟨v, hv, hvval, _, hvmeasure⟩ := exists_polynomialDensityMeasure_extension g
  simp only [koornwinderMeasure]
  rw [integral_map (continuous_koornwinderCoordinates hρ).measurable.aemeasurable
      hi.aestronglyMeasurable,
    integral_map (continuous_koornwinderCoordinates hρ).measurable.aemeasurable
      p.property.aestronglyMeasurable]
  change (∫ x, eval (koornwinderCoordinates ρ x) p.val
      ∂(subtypeDensityMeasure h (μ.comap Subtype.val)).prod
        (polynomialDensityMeasure g (ν.comap Subtype.val))) =
    ∫ x, eval (koornwinderCoordinates ρ x) (u*p.val) ∂μ.prod ν
  rw [hwmeasure, hvmeasure,
    prod_withDensity hw.coe_nnreal_ennreal hv.coe_nnreal_ennreal]
  erw [integral_withDensity_eq_integral_toReal_smul
      ((hw.comp measurable_fst).coe_nnreal_ennreal.mul
        (hv.comp measurable_snd).coe_nnreal_ennreal)
      (Filter.Eventually.of_forall (fun _ => ENNReal.mul_lt_top
        ENNReal.coe_lt_top ENNReal.coe_lt_top))]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hh,
    Measure.quasiMeasurePreserving_snd.ae hg, Measure.quasiMeasurePreserving_fst.ae hu]
    with x hx hz hux
  simp only [Function.comp_apply, Pi.mul_apply, ENNReal.toReal_mul, hwval x.1 hx,
    hvval x.2 hz, ENNReal.coe_toReal, NNReal.coe_mk, smul_eq_mul, map_mul, hux x.2]

/-- The modified pairing is polynomial multiplication in the original pairing. -/
theorem integralInner_koornwinder_modification {μ : Measure D} {ν : Measure ℝ}
    [SFinite ν] {ρ : D → ℝ} (hρ : Continuous ρ)
    (h g : ℝ[X]) (hh : ∀ᵐ (x : D) ∂μ, 0 ≤ h.eval (x : ℝ)) (hg : ∀ᵐ z ∂ν, 0 ≤ g.eval z)
    (u p q : MvPolynomial (Fin 2) ℝ)
    (hu : ∀ᵐ (x : D) ∂μ, ∀ z, eval (koornwinderCoordinates ρ (x,z)) u = h.eval (x : ℝ)*g.eval z)
    (hi : Integrable (fun v => eval v ((u*p)*q)) (koornwinderMeasure ρ μ ν)) :
    integralInner (koornwinderMeasure ρ
      (Polynomial.subtypeDensityMeasure (h) ((μ).comap Subtype.val))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val))) (IntegrablePair.of (koornwinderMeasure ρ
      (Polynomial.subtypeDensityMeasure (h) ((μ).comap Subtype.val))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val))) p q (h := by
        simpa only [map_mul] using
          (integrable_eval_koornwinder_modification_iff hρ h g hh hg u (p*q) hu).2
            (by simpa only [mul_assoc] using hi))) =
      integralInner (koornwinderMeasure ρ μ ν) (IntegrablePair.of (koornwinderMeasure ρ μ ν) (u*p) q (h := by simpa only [map_mul] using hi)) := by
  have he := integral_eval_koornwinder_modification hρ h g hh hg u
    ⟨p*q, by simpa only [mul_assoc] using hi⟩ hu
  simpa only [integralInner, map_mul, mul_assoc] using he

/-- The affine Type 2 density is λρ(x)+μy. -/
theorem koornwinderModificationPolynomial_affine (c : ℝ[X]) (α β : ℝ) :
    koornwinderModificationPolynomial c 1 (Polynomial.C α+Polynomial.C β*Polynomial.X) 1 1 =
      C α*c.eval₂ C (X 0)+C β*X 1 := by
  simp [koornwinderModificationPolynomial, scaledLift, Finset.sum_range_succ]

/-- The square-root Type 2 density is λa(x)+μy², where ρ²=a. -/
theorem koornwinderModificationPolynomial_quadratic (a : ℝ[X]) (α β : ℝ) :
    koornwinderModificationPolynomial a 1 (Polynomial.C α+Polynomial.C β*Polynomial.X^2) 2 1 =
      C α*a.eval₂ C (X 0)+C β*X 1^2 := by
  simp [koornwinderModificationPolynomial, scaledLift, Finset.sum_range_succ]

end MvPolynomial
