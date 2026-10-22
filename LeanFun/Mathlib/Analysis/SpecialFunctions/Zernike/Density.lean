/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalDensity
public import LeanFun.Mathlib.MeasureTheory.Integral.SquaredRadius
import Mathlib.Topology.Algebra.MvPolynomial

/-! # The Zernike disk weight and its radial Jacobian
The standard disk measure has polar density r^(2a) (1-r²)^b r dr dtheta.
Here it is constructed by squared-radius pushforward and identified with this
polar integral, including the exact factor from the Jacobi mass.
Reference: DLMF 18.37.2 (a=0); MultivariateOrthogonalPolynomials.jl, disk.jl.
-/

@[expose] public section
open MeasureTheory Polynomial Set
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- The disk measure with radial weight (r²)^a (1-r²)^b, including the area Jacobian. -/
noncomputable def zernikeMeasure (a b : ℝ) : Measure (Fin 2 → ℝ) :=
  ENNReal.ofReal (((2 : ℝ)^(a+b+2))⁻¹) • zernikeProductMeasure a b

/-- Exact removal of the auxiliary Jacobi mass. -/
theorem integral_zernikeMeasure (a b : ℝ) (f : IntegrableInput (zernikeProductMeasure a b)) :
    ∫ v, f.val v ∂zernikeMeasure a b =
      ((2 : ℝ)^(a+b+2))⁻¹ * ∫ v, f.val v ∂zernikeProductMeasure a b := by
  rw [zernikeMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

private theorem radial_map (a b : ℝ) :
    (Measure.comap NNReal.toReal (unitJacobiMeasure b a)).map NNReal.toReal =
      unitJacobiMeasure b a := by
  have hμ : ∀ᵐ x ∂unitJacobiMeasure b a, x ∈ Ici (0 : ℝ) :=
    (ae_mem_Icc_unitJacobiMeasure b a).mono (fun _ hx ↦ hx.1)
  have he := map_comap_subtype_coe (s := Ici (0 : ℝ))
    (μ := unitJacobiMeasure b a) measurableSet_Ici
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at he
  exact he
private theorem radial_data (a b : ℝ)
    (f : IntegrableInput (Measure.comap NNReal.toReal (unitJacobiMeasure b a)))
    (hf : Measurable f.val) :
    Integrable (fun r : Ioo (0 : ℝ) 1 ↦ (unitJacobiWeight b a r : ℝ) *
      f.val ⟨r,r.property.1.le⟩) volume ∧
    (∫ r, f.val r ∂Measure.comap NNReal.toReal (unitJacobiMeasure b a)) =
      ∫ r : Ioo (0 : ℝ) 1, (unitJacobiWeight b a r : ℝ) * f.val ⟨r,r.property.1.le⟩ := by
  let F : ℝ → ℝ := Function.extend NNReal.toReal f.val (fun _ ↦ 0)
  have hF : Measurable F :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ici).measurable_extend hf measurable_const
  have he (r : NNReal) : F r = f.val r :=
    Subtype.val_injective.extend_apply _ _ r
  have hi : Integrable F (unitJacobiMeasure b a) := by
    rw [← radial_map a b, integrable_map_measure hF.aestronglyMeasurable (by fun_prop)]
    simpa only [Function.comp_def, he] using f.integrable
  have ht := integrable_unitJacobiWeight_mul b a ⟨F,hi⟩ hF
  have hv := integral_unitJacobiMeasure_subtype b a ⟨F,hi⟩ hF
  have her (r : Ioo (0 : ℝ) 1) : F r = f.val ⟨r,r.property.1.le⟩ := he ⟨r,r.property.1.le⟩
  simp only [her] at ht hv
  refine ⟨ht, ?_⟩
  rw [← hv]
  calc
    _ = ∫ r, F (r : ℝ) ∂Measure.comap NNReal.toReal (unitJacobiMeasure b a) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun r ↦ (he r).symm))
    _ = ∫ x, F x ∂(Measure.comap NNReal.toReal (unitJacobiMeasure b a)).map NNReal.toReal :=
      (integral_map (by fun_prop) hF.aestronglyMeasurable).symm
    _ = _ := congrArg (fun μ : Measure ℝ ↦ ∫ x, F x ∂μ) (radial_map a b)

/-- An integrable angular slice at a nonnegative squared radius. -/
noncomputable def zernikeAngularInput (p : MvPolynomial (Fin 2) ℝ) (r : NNReal) :
    IntegrableInput (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
  ⟨fun θ => eval (zernikeCoordinates (r,θ)) p, by
    have hc : Continuous (fun θ => eval (zernikeCoordinates (r,θ)) p) :=
      p.continuous_eval.comp (continuous_zernikeCoordinates.comp (by fun_prop))
    exact (hc.integrableOn_Icc (a := -Real.pi) (b := Real.pi)).mono_set Ioo_subset_Icc_self⟩

private theorem integrable_zernikeRadialIntegral (a b : Ioi (-1 : ℝ)) (p : MvPolynomial (Fin 2) ℝ) :
    Integrable (fun r : NNReal ↦ ∫ θ, (zernikeAngularInput p r).val θ
      ∂volume.restrict (Ioo (-Real.pi) Real.pi))
      (Measure.comap NNReal.toReal (unitJacobiMeasure b a)) := by
  let := isFiniteMeasure_unitJacobiMeasure b.property a.property
  have hp := integrable_zernikeProductMeasure a.property b.property p.continuous_eval
  change Integrable (fun v ↦ eval v p) (Measure.map zernikeCoordinates
    ((Measure.comap NNReal.toReal (unitJacobiMeasure b a)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi)))) at hp
  have hi := (integrable_map_measure p.continuous_eval.aestronglyMeasurable
    continuous_zernikeCoordinates.measurable.aemeasurable).mp hp
  exact hi.integral_prod_left
private theorem measurable_zernikeRadialIntegral (p : MvPolynomial (Fin 2) ℝ) :
    Measurable (fun r : NNReal ↦ ∫ θ, (zernikeAngularInput p r).val θ
      ∂volume.restrict (Ioo (-Real.pi) Real.pi)) :=
  (p.continuous_eval.comp continuous_zernikeCoordinates).stronglyMeasurable.integral_prod_right'.measurable

/-- Internal existence proof for the typed radial integrand. -/
theorem integrable_zernikeSquaredRadius_formula (a b : Ioi (-1 : ℝ))
    (p : MvPolynomial (Fin 2) ℝ) :
    Integrable (fun r : Ioo (0 : ℝ) 1 => (1-(r : ℝ))^(b : ℝ)*(r : ℝ)^(a : ℝ) *
    ∫ θ, (zernikeAngularInput p (NNReal.mk r r.property.1.le)).val θ
      ∂volume.restrict (Ioo (-Real.pi) Real.pi)) volume := by
  have h := (radial_data a b ⟨_,integrable_zernikeRadialIntegral a b p⟩ (measurable_zernikeRadialIntegral p)).1.const_mul
    (((2 : ℝ)^((b : ℝ)+(a : ℝ)+1))⁻¹)
  convert h using 1
  ext r
  rw [unitJacobiWeight_apply]
  field_simp
  rfl

/-- The integrable squared-radius density, with all power bases strictly positive. -/
noncomputable def zernikeSquaredRadiusInput (a b : Ioi (-1 : ℝ))
    (p : MvPolynomial (Fin 2) ℝ) : IntegrableInput (volume : Measure (Ioo (0 : ℝ) 1)) :=
  ⟨fun r : Ioo (0 : ℝ) 1 => (1-(r : ℝ))^(b : ℝ)*(r : ℝ)^(a : ℝ) *
    ∫ θ, (zernikeAngularInput p (NNReal.mk r r.property.1.le)).val θ
      ∂volume.restrict (Ioo (-Real.pi) Real.pi), integrable_zernikeSquaredRadius_formula a b p⟩

/-- Every angular slice has its classical integral. -/
theorem zernikeAngularInput_integrable (p : MvPolynomial (Fin 2) ℝ) (r : NNReal) :
    Integrable (zernikeAngularInput p r).val (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
  (zernikeAngularInput p r).integrable

/-- The weighted squared-radius input is integrable even for singular admissible weights. -/
theorem zernikeSquaredRadiusInput_integrable (a b : Ioi (-1 : ℝ))
    (p : MvPolynomial (Fin 2) ℝ) : Integrable (zernikeSquaredRadiusInput a b p).val volume :=
  (zernikeSquaredRadiusInput a b p).integrable

/-- Squared-radius integration with its area factor, entirely within the classical domain. -/
theorem integral_zernikeMeasure_squaredRadius {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (p : MvPolynomial (Fin 2) ℝ) :
    ∫ v, eval v p ∂zernikeMeasure a b =
      (1/2 : ℝ) * ∫ r : Ioo (0 : ℝ) 1,
        (zernikeSquaredRadiusInput ⟨a,ha⟩ ⟨b,hb⟩ p).val r := by
  let := isFiniteMeasure_unitJacobiMeasure hb ha
  have hp := integrable_zernikeProductMeasure ha hb p.continuous_eval
  change Integrable (fun v ↦ eval v p) (Measure.map zernikeCoordinates
    ((Measure.comap NNReal.toReal (unitJacobiMeasure b a)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi)))) at hp
  have hi := (integrable_map_measure p.continuous_eval.aestronglyMeasurable
    continuous_zernikeCoordinates.measurable.aemeasurable).mp hp
  have he := (radial_data a b ⟨_,integrable_zernikeRadialIntegral ⟨a,ha⟩ ⟨b,hb⟩ p⟩ (measurable_zernikeRadialIntegral p)).2
  rw [zernikeMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    zernikeProductMeasure, integral_map continuous_zernikeCoordinates.measurable.aemeasurable
      p.continuous_eval.aestronglyMeasurable]
  change ((2 : ℝ)^(a+b+2))⁻¹ *
    (∫ v : NNReal × ℝ, eval (zernikeCoordinates v) p
      ∂(Measure.comap NNReal.toReal (unitJacobiMeasure b a)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi))) = _
  change Integrable (fun v : NNReal × ℝ ↦ eval (zernikeCoordinates v) p)
    ((Measure.comap NNReal.toReal (unitJacobiMeasure b a)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi))) at hi
  rw [integral_prod _ hi]
  change ((2 : ℝ)^(a+b+2))⁻¹ *
    (∫ r : NNReal, ∫ θ, (zernikeAngularInput p r).val θ
      ∂volume.restrict (Ioo (-Real.pi) Real.pi)
      ∂Measure.comap NNReal.toReal (unitJacobiMeasure b a)) = _
  rw [he, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [unitJacobiWeight_apply]
  change ((2 : ℝ)^(a+b+2))⁻¹ * ((2 : ℝ)^(b+a+1) * _ * _) = (1/2 : ℝ) * (_ * _)
  rw [show a+b+2 = (b+a+1)+1 by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  field_simp
  rfl

/-- Internal integrability proof for the ordinary polar-radius formula. -/
theorem integrable_zernikePolar_formula (a b : Ioi (-1 : ℝ))
    (p : MvPolynomial (Fin 2) ℝ) : Integrable (fun r : Ioo (0 : ℝ) 1 => (r : ℝ)*((r : ℝ)^2)^(a : ℝ)*(1-(r : ℝ)^2)^(b : ℝ) *
    ∫ θ, (zernikeAngularInput p (NNReal.mk ((r : ℝ)^2) (sq_nonneg _))).val θ
      ∂volume.restrict (Ioo (-Real.pi) Real.pi)) volume := by
  have h := ((integral_unitInterval_sq (zernikeSquaredRadiusInput a b p)).1).const_mul (1/2 : ℝ)
  convert h using 1
  ext r
  simp only [zernikeSquaredRadiusInput, zernikeAngularInput, zernikeCoordinates, NNReal.coe_mk]
  ring

/-- The ordinary polar-radius density with its area Jacobian and integrability certificate. -/
noncomputable def zernikePolarInput (a b : Ioi (-1 : ℝ))
    (p : MvPolynomial (Fin 2) ℝ) : IntegrableInput (volume : Measure (Ioo (0 : ℝ) 1)) :=
  ⟨fun r : Ioo (0 : ℝ) 1 => (r : ℝ)*((r : ℝ)^2)^(a : ℝ)*(1-(r : ℝ)^2)^(b : ℝ) *
    ∫ θ, (zernikeAngularInput p (NNReal.mk ((r : ℝ)^2) (sq_nonneg _))).val θ
      ∂volume.restrict (Ioo (-Real.pi) Real.pi), integrable_zernikePolar_formula a b p⟩

/-- The polar-radius input is classically integrable throughout the admissible parameter range. -/
theorem zernikePolarInput_integrable (a b : Ioi (-1 : ℝ))
    (p : MvPolynomial (Fin 2) ℝ) : Integrable (zernikePolarInput a b p).val volume :=
  (zernikePolarInput a b p).integrable

/-- Polar integration with its Jacobian, with no evaluation outside the classical radial domain. -/
theorem integral_zernikeMeasure_polar {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (p : MvPolynomial (Fin 2) ℝ) :
    ∫ v, eval v p ∂zernikeMeasure a b =
      ∫ r : Ioo (0 : ℝ) 1, (zernikePolarInput ⟨a,ha⟩ ⟨b,hb⟩ p).val r := by
  rw [integral_zernikeMeasure_squaredRadius ha hb,
    (integral_unitInterval_sq (zernikeSquaredRadiusInput ⟨a,ha⟩ ⟨b,hb⟩ p)).2,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [zernikePolarInput, zernikeSquaredRadiusInput,
    zernikeAngularInput, zernikeCoordinates, NNReal.coe_mk]
  ring

/-- Every polynomial has finite square integral for the standard disk measure. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_zernikeMeasure {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    HasFiniteMoments (zernikeMeasure a b) := by
  intro p
  exact (hasFiniteMoments_zernikeProductMeasure ha hb p).smul_measure ENNReal.ofReal_ne_top

end MvPolynomial
