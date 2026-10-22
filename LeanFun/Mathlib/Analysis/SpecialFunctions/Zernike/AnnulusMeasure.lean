/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusRadial
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Density
import Mathlib.Topology.Algebra.MvPolynomial

/-! # The annular Zernike measure
The squared inner radius is q in (0,1). The standard polar weight is
(1-r²)^a(r²-q)^b, including the area Jacobian. The semiclassical pushforward
construction is identified explicitly with integration in squared radius.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public section
open MeasureTheory Set Polynomial
open scoped ENNReal
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- Annular coordinates on their full classical affine-radius domain. -/
noncomputable def zernikeAnnulusCoordinates (q : {q : ℝ // q ≠ 1})
    (v : {v : ℝ × ℝ // 0 ≤ 1-v.1/annulusParameter q}) : Fin 2 → ℝ :=
  zernikeCoordinates (NNReal.mk (1-v.val.1/annulusParameter q) v.property,v.val.2)

/-- The annular chart is continuous on its classical domain. -/
theorem continuous_zernikeAnnulusCoordinates (q : {q : ℝ // q ≠ 1}) :
    Continuous (zernikeAnnulusCoordinates q) := by
  unfold zernikeAnnulusCoordinates
  exact continuous_zernikeCoordinates.comp (by unfold NNReal.mk; fun_prop)

/-- The entire unit parameter interval has a nonnegative squared radius. -/
theorem zernikeAnnulusCoordinates_radical_nonneg
    (q : {q : ℝ // 0 ≤ q ∧ q ≠ 1}) (x : Icc (0 : ℝ) 1) :
    0 ≤ 1-(x : ℝ)/annulusParameter ⟨q,q.property.2⟩ := by
  have he : 1-(x : ℝ)/annulusParameter ⟨q,q.property.2⟩ =
      (1-(x : ℝ))+(q : ℝ)*(x : ℝ) := by
    simp only [annulusParameter, div_inv_eq_mul]
    ring
  rw [he]
  exact add_nonneg (sub_nonneg.mpr x.property.2) (mul_nonneg q.property.1 x.property.1)

/-- The auxiliary product pushforward, including all nonnegative nondegenerate radii. -/
noncomputable def zernikeAnnulusProductMeasure
    (q : {q : ℝ // 0 ≤ q ∧ q ≠ 1}) (a b : ℝ) : Measure (Fin 2 → ℝ) :=
  let μ := Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ)
    (semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0)
  let ν := ProductMeasureInput.ofSFinite μ (volume.restrict (Ioo (-Real.pi) Real.pi))
  Measure.map (fun v : Icc (0 : ℝ) 1 × ℝ =>
    zernikeAnnulusCoordinates ⟨q,q.property.2⟩
      ⟨((v.1 : ℝ),v.2),zernikeAnnulusCoordinates_radical_nonneg q v.1⟩) (μ.prod ν.inner)

/-- The standard interior annular measure, including the disk endpoint q=0. -/
noncomputable def zernikeAnnulusMeasure (q : Ico (0 : ℝ) 1) (a b : ℝ) : Measure (Fin 2 → ℝ) :=
  ENNReal.ofReal ((1/2 : ℝ)*((annulusParameter ⟨q,ne_of_lt q.property.2⟩)^(a+b+1))⁻¹) •
    zernikeAnnulusProductMeasure ⟨q, q.property.1, ne_of_lt q.property.2⟩ a b



/-- Continuous functions are integrable on the compact annular parameter support. -/
theorem integrable_zernikeAnnulusProductMeasure {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (zernikeAnnulusProductMeasure ⟨q,hq.1.le,ne_of_lt hq.2⟩ a b) := by
  let := isFiniteMeasure_semiclassicalJacobiMeasure (t := 2) (γ := 0) (by norm_num) ha hb
  let C : Icc (0 : ℝ) 1 × ℝ → Fin 2 → ℝ := fun v ↦
    zernikeAnnulusCoordinates ⟨q,ne_of_lt hq.2⟩
      ⟨((v.1 : ℝ),v.2),zernikeAnnulusCoordinates_radical_nonneg
        ⟨q,hq.1.le,ne_of_lt hq.2⟩ v.1⟩
  have hC : Continuous C := continuous_zernikeAnnulusCoordinates _ |>.comp (by fun_prop)
  change Integrable f (Measure.map C ((Measure.comap
    (Subtype.val : Icc (0 : ℝ) 1 → ℝ)
    (semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi))))
  rw [integrable_map_measure hf.aestronglyMeasurable hC.measurable.aemeasurable]
  have hi := (hf.comp hC).continuousOn.integrableOn_compact
    (μ := (Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ)
      (semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi)))
    (isCompact_univ.prod isCompact_Icc :
      IsCompact (univ ×ˢ Icc (-Real.pi) Real.pi : Set (Icc (0 : ℝ) 1 × ℝ)))
  have hs : ∀ᵐ v ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ)
      (semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi)),
      v ∈ (univ ×ˢ Icc (-Real.pi) Real.pi : Set (Icc (0 : ℝ) 1 × ℝ)) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem measurableSet_Ioo)] with v hθ
    exact ⟨mem_univ _,hθ.1.le,hθ.2.le⟩
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at hi

/-- Internal pullback through coordinates with positive squared radius. -/
private theorem annulusProduct_eq_map_open
    (q : {q : ℝ // 0 ≤ q ∧ q ≠ 1}) (a b : ℝ) :
    zernikeAnnulusProductMeasure q a b = Measure.map
      (fun v : Ioo (0 : ℝ) 1 × ℝ ↦
        (![Real.sqrt (1-(v.1 : ℝ)/annulusParameter ⟨q,q.property.2⟩)*Real.cos v.2,
          Real.sqrt (1-(v.1 : ℝ)/annulusParameter ⟨q,q.property.2⟩)*Real.sin v.2] : Fin 2 → ℝ))
      ((volume.withDensity fun x : Ioo (0 : ℝ) 1 ↦
        (semiclassicalJacobiWeight ⟨2,by norm_num⟩ a b 0 x : ℝ≥0∞)).prod
          (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  let ι : Ioo (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun x ↦ ⟨x,x.property.1.le,x.property.2.le⟩
  have hι : Measurable ι := by fun_prop
  have hm : Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ)
      (semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0) =
      Measure.map ι (volume.withDensity fun x : Ioo (0 : ℝ) 1 ↦
        (semiclassicalJacobiWeight ⟨2,by norm_num⟩ a b 0 x : ℝ≥0∞)) := by
    apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
    rw [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem
        ((ae_mem_Ioo_semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0).mono
          (fun _ hx ↦ (show _ ∈ Icc (0 : ℝ) 1 from ⟨hx.1.le,hx.2.le⟩))),
      Measure.map_map measurable_subtype_coe hι]
    rfl
  unfold zernikeAnnulusProductMeasure
  dsimp only [ProductMeasureInput.ofSFinite]
  rw [hm]
  conv_lhs => arg 2; arg 2; rw [← Measure.map_id (μ := volume.restrict (Ioo (-Real.pi) Real.pi))]
  rw [Measure.map_prod_map _ _ hι measurable_id,
    Measure.map_map (show Measurable (fun v : Icc (0 : ℝ) 1 × ℝ ↦
      zernikeAnnulusCoordinates ⟨q,q.property.2⟩
        ⟨((v.1 : ℝ),v.2),zernikeAnnulusCoordinates_radical_nonneg q v.1⟩) from
      (continuous_zernikeAnnulusCoordinates _ |>.comp (by fun_prop)).measurable)
      (hι.prodMap measurable_id)]
  rfl

/-- All polynomial moments exist for the auxiliary product measure. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_zernikeAnnulusProductMeasure {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) : HasFiniteMoments (zernikeAnnulusProductMeasure ⟨q,hq.1.le,ne_of_lt hq.2⟩ a b) :=
  fun p ↦ integrable_zernikeAnnulusProductMeasure hq ha hb (p.continuous_eval.pow 2)

/-- All polynomial moments exist for the standard annular measure. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_zernikeAnnulusMeasure {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) : HasFiniteMoments (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) :=
  fun p ↦ (hasFiniteMoments_zernikeAnnulusProductMeasure hq ha hb p).smul_measure
    ENNReal.ofReal_ne_top

/-- A classical scalar pullback, extended by zero only inside this proof. -/
private theorem annulusProduct_classical_input (q : Ioo (0 : ℝ) 1)
    (a b : Ioi (-1 : ℝ)) (p : MvPolynomial (Fin 2) ℝ) :
    ∃ f : IntegrableInput (semiclassicalJacobiMeasure
        ⟨annulusParameter ⟨q,ne_of_lt q.property.2⟩,one_lt_annulusParameter q.property⟩ a b 0),
      (∀ x : Ioo (0 : ℝ) 1, f.val x = ∫ θ in Ioo (-Real.pi) Real.pi,
        eval (![Real.sqrt (1-(x : ℝ)/annulusParameter ⟨q,ne_of_lt q.property.2⟩)*Real.cos θ,
          Real.sqrt (1-(x : ℝ)/annulusParameter ⟨q,ne_of_lt q.property.2⟩)*Real.sin θ] : Fin 2 → ℝ) p) ∧
      (∫ v, eval v p ∂zernikeAnnulusProductMeasure ⟨q,q.property.1.le,ne_of_lt q.property.2⟩ a b) =
        ∫ x, f.val x ∂semiclassicalJacobiMeasure
          ⟨annulusParameter ⟨q,ne_of_lt q.property.2⟩,one_lt_annulusParameter q.property⟩ a b 0 := by
  let t := annulusParameter ⟨q,ne_of_lt q.property.2⟩
  let w := semiclassicalJacobiWeight ⟨2,by norm_num⟩ (a : ℝ) b 0
  let μ : Measure (Ioo (0 : ℝ) 1) := volume.withDensity (fun x ↦ (w x : ℝ≥0∞))
  let ν := volume.restrict (Ioo (-Real.pi) Real.pi)
  let C : Ioo (0 : ℝ) 1 × ℝ → Fin 2 → ℝ := fun v ↦
    ![Real.sqrt (1-(v.1 : ℝ)/t)*Real.cos v.2,Real.sqrt (1-(v.1 : ℝ)/t)*Real.sin v.2]
  have hC : Measurable C := by fun_prop
  have hmap : zernikeAnnulusProductMeasure ⟨q,q.property.1.le,ne_of_lt q.property.2⟩ a b =
      Measure.map C (μ.prod ν) := annulusProduct_eq_map_open _ _ _
  let := isFiniteMeasure_semiclassicalJacobiMeasure (t := 2) (γ := 0)
    (by norm_num) a.property b.property
  let : IsFiniteMeasure μ :=
    (Measure.isFiniteMeasure_map_iff measurable_subtype_coe.aemeasurable).1
      (show IsFiniteMeasure (Measure.map (Subtype.val : Ioo (0 : ℝ) 1 → ℝ) μ) from
        inferInstanceAs (IsFiniteMeasure (semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0)))
  have hp := integrable_zernikeAnnulusProductMeasure q.property a.property b.property p.continuous_eval
  rw [hmap] at hp
  have hc := (integrable_map_measure p.continuous_eval.aestronglyMeasurable hC.aemeasurable).1 hp
  let F : Ioo (0 : ℝ) 1 → ℝ := fun x ↦ ∫ θ, eval (C (x,θ)) p ∂ν
  have hf : Integrable F μ := hc.integral_prod_left
  have hw : Integrable (fun x ↦ (w x : ℝ)*F x) volume := by
    dsimp only [μ] at hf
    rw [integrable_withDensity_iff_integrable_coe_smul w.continuous.measurable] at hf
    simpa only [NNReal.smul_def, smul_eq_mul] using hf
  let G : ℝ → ℝ := fun x ↦ if h : x ∈ Ioo (0 : ℝ) 1 then F ⟨x,h⟩ else 0
  have hg : Integrable G (semiclassicalJacobiMeasure
      ⟨t,one_lt_annulusParameter q.property⟩ a b 0) := by
    rw [semiclassicalJacobiMeasure_zero_third, integrable_semiclassicalJacobiMeasure_iff]
    convert hw using 1
    funext x
    simp only [G, dite_eq_left x.property]
    rfl
  refine ⟨⟨G,hg⟩, ?_, ?_⟩
  · intro x
    change G x = _
    simp only [G, dite_eq_left x.property]
    rfl
  · rw [hmap, integral_map hC.aemeasurable p.continuous_eval.aestronglyMeasurable]
    erw [integral_prod _ hc]
    change (∫ x, F x ∂μ) = ∫ x, G x ∂semiclassicalJacobiMeasure
      ⟨t,one_lt_annulusParameter q.property⟩ a b 0
    rw [semiclassicalJacobiMeasure_zero_third,
      integral_semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0
        ⟨G,by simpa only [semiclassicalJacobiMeasure_zero_third] using hg⟩]
    dsimp only [μ]
    rw [integral_withDensity_eq_integral_smul w.continuous.measurable]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [NNReal.smul_def, smul_eq_mul, G, dite_eq_left x.property]
    rfl

/-- Internal existence proof for the annular radial integrand. -/
theorem integrable_zernikeAnnulusSquaredRadius_formula (q : Ioo (0 : ℝ) 1)
    (a b : Ioi (-1 : ℝ)) (p : MvPolynomial (Fin 2) ℝ) :
    Integrable (fun s : Ioo (q : ℝ) 1 => (1-(s : ℝ))^(a : ℝ)*((s : ℝ)-q)^(b : ℝ) *
      ∫ θ, (zernikeAngularInput p
        (NNReal.mk s (le_trans q.property.1.le s.property.1.le))).val θ
        ∂volume.restrict (Ioo (-Real.pi) Real.pi)) volume := by
  obtain ⟨f,hf,_⟩ := annulusProduct_classical_input q a b p
  have hj := integrable_semiclassicalJacobiMeasure_annulus q a b 0
    ⟨f.val,by simpa only [Nat.cast_zero] using f.property⟩
  simp only [pow_zero, mul_one] at hj
  convert hj using 1
  funext s
  have ht : 0 < annulusParameter ⟨q,ne_of_lt q.property.2⟩ :=
    lt_trans zero_lt_one (one_lt_annulusParameter q.property)
  have he := annulusParameter_mul q (ne_of_lt q.property.2)
  have hx : annulusParameter ⟨q,ne_of_lt q.property.2⟩*(1-(s : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos ht (sub_pos.mpr s.property.2)
    · nlinarith [mul_pos ht (sub_pos.mpr s.property.1)]
  have hv := hf ⟨_,hx⟩
  simp only [mul_div_cancel_left₀ _ ht.ne', sub_sub_cancel] at hv
  rw [hv]
  rfl

/-- The annular squared-radius density, with integrability and strictly positive weight bases. -/
noncomputable def zernikeAnnulusSquaredRadiusInput (q : Ioo (0 : ℝ) 1)
    (a b : Ioi (-1 : ℝ)) (p : MvPolynomial (Fin 2) ℝ) :
    IntegrableInput (volume : Measure (Ioo (q : ℝ) 1)) :=
  ⟨fun s : Ioo (q : ℝ) 1 => (1-(s : ℝ))^(a : ℝ)*((s : ℝ)-q)^(b : ℝ) *
      ∫ θ, (zernikeAngularInput p
        (NNReal.mk s (le_trans q.property.1.le s.property.1.le))).val θ
        ∂volume.restrict (Ioo (-Real.pi) Real.pi), integrable_zernikeAnnulusSquaredRadius_formula q a b p⟩

/-- Admissible annular radial inputs have a classical integral. -/
theorem zernikeAnnulusSquaredRadiusInput_integrable (q : Ioo (0 : ℝ) 1)
    (a b : Ioi (-1 : ℝ)) (p : MvPolynomial (Fin 2) ℝ) :
    Integrable (zernikeAnnulusSquaredRadiusInput q a b p).val volume :=
  (zernikeAnnulusSquaredRadiusInput q a b p).integrable

/-- The classical annular density formula, including admissible endpoint singularities. -/
theorem integral_zernikeAnnulusMeasure_squaredRadius {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1 < a) (hb : -1 < b) (p : MvPolynomial (Fin 2) ℝ) :
    ∫ v, eval v p ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b =
      (1/2 : ℝ)*∫ s : Ioo q 1,
        (zernikeAnnulusSquaredRadiusInput ⟨q,hq⟩ ⟨a,ha⟩ ⟨b,hb⟩ p).val s := by
  obtain ⟨f,hf,hM⟩ := annulusProduct_classical_input ⟨q,hq⟩ ⟨a,ha⟩ ⟨b,hb⟩ p
  have ht : 0 < annulusParameter ⟨q,ne_of_lt hq.2⟩ :=
    lt_trans zero_lt_one (one_lt_annulusParameter hq)
  have he := annulusParameter_mul q (ne_of_lt hq.2)
  have hi := integral_semiclassicalJacobiMeasure_annulus ⟨q,hq⟩ a b 0
    ⟨f.val,by simpa only [Nat.cast_zero] using f.property⟩
  simp only [Nat.cast_zero, add_zero, pow_zero, mul_one] at hi
  rw [zernikeAnnulusMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul, hM, hi,
    ← mul_assoc, mul_assoc (1/2 : ℝ), inv_mul_cancel₀ (by positivity), mul_one]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with s
  have hx : annulusParameter ⟨q,ne_of_lt hq.2⟩*(1-(s : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos ht (sub_pos.mpr s.property.2)
    · nlinarith [mul_pos ht (sub_pos.mpr s.property.1)]
  have hv := hf ⟨_,hx⟩
  simp only [mul_div_cancel_left₀ _ ht.ne', sub_sub_cancel] at hv
  rw [hv]
  rfl

end MvPolynomial
