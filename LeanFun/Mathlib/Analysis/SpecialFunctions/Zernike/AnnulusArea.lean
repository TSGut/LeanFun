/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusMeasure
import Mathlib.Analysis.SpecialFunctions.PolarCoord
/-! # Annular area measure

The unweighted polar pushforward is planar Lebesgue measure restricted to the
open annulus. The semiclassical coordinate has constant absolute Jacobian
`1 / (2 * t)`; the excluded polar ray is null.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public section
open MeasureTheory Set Real
attribute [local instance] Measure.Subtype.measureSpace
open Filter
open scoped Topology
namespace MvPolynomial
noncomputable section
private def safeAreaChart (t : Ioi (1 : ℝ)) (p : ℝ × ℝ) : ℝ × ℝ := by
  classical
  exact if h : 0 < 1-p.1/(t : ℝ) then
    polarCoord.symm ((NNReal.sqrt ⟨1-p.1/(t : ℝ), h.le⟩ : ℝ), p.2) else 0
private theorem measurable_safeAreaChart (t : Ioi (1 : ℝ)) :
    Measurable (safeAreaChart t) := by
  classical
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < 1-p.1/(t : ℝ)} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  exact Measurable.dite
    (f := fun p : {p : ℝ × ℝ | 0 < 1-p.1/(t : ℝ)} ↦
      polarCoord.symm ((NNReal.sqrt ⟨1-p.val.1/(t : ℝ),p.property.le⟩ : ℝ),p.val.2))
    (by fun_prop) measurable_const hs
private theorem safeAreaChart_eq (t : Ioi (1 : ℝ)) (p : ℝ × ℝ)
    (hp : 0 < 1-p.1/(t : ℝ)) :
    safeAreaChart t p = polarCoord.symm (Real.sqrt (1-p.1/(t : ℝ)),p.2) := by
  classical
  rw [safeAreaChart, dite_eq_left hp]
  have hr : (NNReal.sqrt ⟨1-p.1/(t : ℝ),hp.le⟩ : ℝ) = Real.sqrt (1-p.1/(t : ℝ)) := Real.coe_sqrt
  rw [hr]
private theorem safeAreaChart_local (t : Ioi (1 : ℝ)) (p : ℝ × ℝ)
    (hp : 0 < 1-p.1/(t : ℝ)) :
    safeAreaChart t =ᶠ[𝓝 p] fun v ↦ polarCoord.symm (Real.sqrt (1-v.1/(t : ℝ)),v.2) := by
  have hnear : ∀ᶠ v in 𝓝 p, 0 < 1-v.1/(t : ℝ) :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hp
  filter_upwards [hnear] with v hv
  exact safeAreaChart_eq t v hv

private theorem radial_hasDeriv (t : ℝ) (p : ℝ × ℝ) (_ht : t ≠ 0) (hp : 0 < 1-p.1/t) :
    HasFDerivAt ((fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t) ((fun (t : ℝ) (p : ℝ × ℝ) => (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![-(t⁻¹)/(2*Real.sqrt (1-p.1/t)),0;0,1]).toContinuousLinearMap) t p) p := by
  have hlin : HasFDerivAt (fun p : ℝ × ℝ ↦ 1-p.1/t)
      (-(t⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_smul t⁻¹).const_sub 1
  have hs := (hasDerivAt_sqrt hp.ne').comp_hasFDerivAt p hlin
  have he : (fun (t : ℝ) (p : ℝ × ℝ) => (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![-(t⁻¹)/(2*Real.sqrt (1-p.1/t)),0;0,1]).toContinuousLinearMap) t p =
      ((1 / (2 * √(1-p.1/t))) • -(t⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    dsimp only
    rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
    apply ContinuousLinearMap.ext
    intro v
    change ((-(t⁻¹)/(2*√(1-p.1/t)))*v.1+0*v.2, 0*v.1+1*v.2) =
      ((1/(2*√(1-p.1/t)))* -(t⁻¹*v.1), v.2)
    congr 1 <;> ring
  rw [he]
  exact hs.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
private theorem radial_det (t : ℝ) (p : ℝ × ℝ) (_ht : t ≠ 0) (_hp : 0 < 1-p.1/t) :
    ((fun (t : ℝ) (p : ℝ × ℝ) => (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![-(t⁻¹)/(2*Real.sqrt (1-p.1/t)),0;0,1]).toContinuousLinearMap) t p).det = -(t⁻¹)/(2*√(1-p.1/t)) := by
  simp [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
private theorem area_hasDeriv (t : ℝ) (p : ℝ × ℝ) (ht : t ≠ 0) (hp : 0 < 1-p.1/t) :
    HasFDerivAt ((fun (t : ℝ) => polarCoord.symm ∘ (fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t) t) ((fun (t : ℝ) (p : ℝ × ℝ) => (fderivPolarCoordSymm ((fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t p)).comp ((fun (t : ℝ) (p : ℝ × ℝ) => (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![-(t⁻¹)/(2*Real.sqrt (1-p.1/t)),0;0,1]).toContinuousLinearMap) t p)) t p) p :=
  (hasFDerivAt_polarCoord_symm _).comp p (radial_hasDeriv t p ht hp)
private theorem area_det (t : ℝ) (p : ℝ × ℝ) (ht : t ≠ 0) (hp : 0 < 1-p.1/t) :
    ((fun (t : ℝ) (p : ℝ × ℝ) => (fderivPolarCoordSymm ((fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t p)).comp ((fun (t : ℝ) (p : ℝ × ℝ) => (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![-(t⁻¹)/(2*Real.sqrt (1-p.1/t)),0;0,1]).toContinuousLinearMap) t p)) t p).det = -(t⁻¹)/2 := by
  change LinearMap.det ((fderivPolarCoordSymm ((fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t p)).toLinearMap.comp
    ((fun (t : ℝ) (p : ℝ × ℝ) => (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![-(t⁻¹)/(2*Real.sqrt (1-p.1/t)),0;0,1]).toContinuousLinearMap) t p).toLinearMap) = _
  rw [LinearMap.det_comp]
  change (fderivPolarCoordSymm ((fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t p)).det * ((fun (t : ℝ) (p : ℝ × ℝ) => (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![-(t⁻¹)/(2*Real.sqrt (1-p.1/t)),0;0,1]).toContinuousLinearMap) t p).det = _
  rw [det_fderivPolarCoordSymm, radial_det t p ht hp]
  dsimp
  generalize hr : Real.sqrt (1-p.1/t) = r
  have hr0 : r ≠ 0 := hr ▸ (Real.sqrt_pos.mpr hp).ne'
  field_simp [hr0]

private def safeAreaDerivative (t : Ioi (1 : ℝ)) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := by
  classical
  exact if hp : 0 < 1-p.1/(t : ℝ) then
    (fderivPolarCoordSymm ((NNReal.sqrt ⟨1-p.1/(t : ℝ),hp.le⟩ : ℝ),p.2)).comp
      (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
        !![-((t : ℝ)⁻¹)/(2*(NNReal.sqrt ⟨1-p.1/(t : ℝ),hp.le⟩ : ℝ)),0;0,1]).toContinuousLinearMap
    else 0
private theorem hasFDerivAt_safeAreaChart (t : Ioi (1 : ℝ)) (p : ℝ × ℝ)
    (hp : 0 < 1-p.1/(t : ℝ)) :
    HasFDerivAt (safeAreaChart t) (safeAreaDerivative t p) p := by
  classical
  rw [safeAreaDerivative, dite_eq_left hp]
  have hr : (NNReal.sqrt ⟨1-p.1/(t : ℝ),hp.le⟩ : ℝ) = Real.sqrt (1-p.1/(t : ℝ)) := Real.coe_sqrt
  rw [hr]
  exact (area_hasDeriv (t : ℝ) p (ne_of_gt (lt_trans zero_lt_one t.property)) hp).congr_of_eventuallyEq
    (safeAreaChart_local t p hp)
private theorem det_safeAreaDerivative (t : Ioi (1 : ℝ)) (p : ℝ × ℝ)
    (hp : 0 < 1-p.1/(t : ℝ)) :
    (safeAreaDerivative t p).det = -((t : ℝ)⁻¹)/2 := by
  classical
  rw [safeAreaDerivative, dite_eq_left hp]
  have hr : (NNReal.sqrt ⟨1-p.1/(t : ℝ),hp.le⟩ : ℝ) = Real.sqrt (1-p.1/(t : ℝ)) := Real.coe_sqrt
  rw [hr]
  exact area_det (t : ℝ) p (ne_of_gt (lt_trans zero_lt_one t.property)) hp

private theorem area_inj {t : ℝ} (ht : 1 < t) :
    InjOn ((fun (t : ℝ) => polarCoord.symm ∘ (fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t) t) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) := by
  intro p hp z hz he
  have hr (v : ℝ × ℝ) (hv : v ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) :
      (fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t v ∈ polarCoord.target := by
    refine ⟨Real.sqrt_pos.mpr ?_, hv.2⟩
    have := (div_lt_one (by linarith : 0 < t)).mpr (lt_trans hv.1.2 ht)
    linarith
  have he' := polarCoord.symm.injOn (hr p hp) (hr z hz) he
  have he1 := congrArg Prod.fst he'
  have he2 := congrArg Prod.snd he'
  have hp0 : 0 < 1-p.1/t := Real.sqrt_pos.mp (hr p hp).1
  have hz0 : 0 < 1-z.1/t := Real.sqrt_pos.mp (hr z hz).1
  have hs := congrArg (fun x : ℝ ↦ x^2) he1
  dsimp at hs he2
  rw [Real.sq_sqrt hp0.le, Real.sq_sqrt hz0.le] at hs
  have heq : p.1/t = z.1/t := by linarith
  exact Prod.ext ((div_left_inj' (by linarith : t ≠ 0)).mp heq) he2
private theorem area_image {t : ℝ} (ht : 1 < t) :
    (fun (t : ℝ) => polarCoord.symm ∘ (fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t) t '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) =
      {z : ℝ × ℝ | 1-t⁻¹ < z.1^2+z.2^2 ∧ z.1^2+z.2^2 < 1} ∩
        polarCoord.source := by
  have ht0 : 0 < t := by linarith
  have htn : t ≠ 0 := ht0.ne'
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hr : 0 < 1-p.1/t := by
      have := (div_lt_one ht0).mpr (lt_trans hp.1.2 ht)
      linarith
    have hsq : ((fun (t : ℝ) => polarCoord.symm ∘ (fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t) t p).1^2+((fun (t : ℝ) => polarCoord.symm ∘ (fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t) t p).2^2 = 1-p.1/t := by
      dsimp [polarCoord]
      rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq,
        mul_one, Real.sq_sqrt hr.le]
    refine ⟨?_, polarCoord.map_target ⟨Real.sqrt_pos.mpr hr, hp.2⟩⟩
    change 1-t⁻¹ < _ ∧ _ < 1
    rw [hsq]
    constructor
    · have := (div_lt_div_iff_of_pos_right ht0).mpr hp.1.2
      simpa only [one_div] using sub_lt_sub_left this 1
    · have := div_pos hp.1.1 ht0
      linarith
  · rintro ⟨hz, hsource⟩
    let r := (polarCoord z).1
    have hr : 0 < r := (polarCoord.map_source hsource).1
    have hs : r^2 = z.1^2+z.2^2 := by
      exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    refine ⟨(t*(1-r^2), (polarCoord z).2), ?_, ?_⟩
    · refine ⟨⟨mul_pos ht0 (by linarith [hz.2]), ?_⟩,
        (polarCoord.map_source hsource).2⟩
      have := mul_lt_mul_of_pos_left hz.1 ht0
      have hti : t*t⁻¹ = 1 := mul_inv_cancel₀ htn
      nlinarith
    · have he : (fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t (t*(1-r^2), (polarCoord z).2) = polarCoord z := by
        apply Prod.ext
        · dsimp
          rw [mul_div_cancel_left₀ _ htn, sub_sub_cancel, Real.sqrt_sq hr.le]
        · rfl
      change polarCoord.symm ((fun (t : ℝ) (p : ℝ × ℝ) => (Real.sqrt (1-p.1/t),p.2)) t _) = z
      rw [he, polarCoord.left_inv hsource]
private theorem safeArea_map_measure (t : Ioi (1 : ℝ)) :
    ENNReal.ofReal ((t : ℝ)⁻¹/2) • Measure.map (safeAreaChart t)
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)) =
      volume.restrict {z : ℝ × ℝ | 1-(t : ℝ)⁻¹ < z.1^2+z.2^2 ∧ z.1^2+z.2^2 < 1} := by
  have hd (p : ℝ × ℝ) (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) :
      0 < 1-p.1/(t : ℝ) := by
    have := (div_lt_one (lt_trans zero_lt_one t.property)).mpr (lt_trans hp.1.2 t.property)
    linarith
  have heq : EqOn (safeAreaChart t)
      (fun p : ℝ × ℝ ↦ polarCoord.symm (Real.sqrt (1-p.1/(t : ℝ)),p.2))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) :=
    fun p hp ↦ safeAreaChart_eq t p (hd p hp)
  have h := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure (ℝ × ℝ))
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet
    (fun p hp ↦ (hasFDerivAt_safeAreaChart t p (hd p hp)).hasFDerivWithinAt)
    ((area_inj t.property).congr heq.symm)
  have hw : (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)).withDensity
      (fun p ↦ ENNReal.ofReal |(safeAreaDerivative t p).det|) =
      ENNReal.ofReal ((t : ℝ)⁻¹/2) •
        volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) := by
    rw [← withDensity_const]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    rw [det_safeAreaDerivative t p (hd p hp), neg_div, abs_neg,
      abs_of_nonneg (div_nonneg (inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one t.property))) (by norm_num))]
  have himg := area_image t.property
  dsimp only [Function.comp_def] at himg
  rw [hw, Measure.map_smul _ (measurable_safeAreaChart t).aemeasurable,
    Set.image_congr heq, himg] at h
  rw [h]
  apply Measure.restrict_congr_set
  filter_upwards [polarCoord_source_ae_eq_univ] with z hz
  have hz' : z ∈ polarCoord.source := of_eq_true hz
  simp only [mem_inter_iff, hz', and_true, mem_ofPred_eq]

private theorem safeArea_product_measure (q : Ioo (0 : ℝ) 1) (a b : ℝ) :
    zernikeAnnulusProductMeasure ⟨q,q.property.1.le,ne_of_lt q.property.2⟩ a b =
      Measure.map ((MeasurableEquiv.finTwoArrow.symm : (ℝ × ℝ) ≃ᵐ (Fin 2 → ℝ)) ∘
        safeAreaChart ⟨Polynomial.annulusParameter ⟨q,ne_of_lt q.property.2⟩,
          Polynomial.one_lt_annulusParameter q.property⟩)
        ((Polynomial.semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0).prod
          (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  let t : Ioi (1 : ℝ) := ⟨Polynomial.annulusParameter ⟨q,ne_of_lt q.property.2⟩,
    Polynomial.one_lt_annulusParameter q.property⟩
  let e : (ℝ × ℝ) ≃ᵐ (Fin 2 → ℝ) := MeasurableEquiv.finTwoArrow.symm
  have hμ : ∀ᵐ x ∂Polynomial.semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0,
      x ∈ Icc (0 : ℝ) 1 :=
    (Polynomial.ae_mem_Ioo_semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0).mono
      (fun _ hx ↦ ⟨hx.1.le,hx.2.le⟩)
  have he := map_comap_subtype_coe (s := Icc (0 : ℝ) 1)
    (μ := Polynomial.semiclassicalJacobiMeasure ⟨2,by norm_num⟩ a b 0) measurableSet_Icc
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at he
  have hm : Measurable (e ∘ safeAreaChart t) := e.measurable.comp (measurable_safeAreaChart t)
  conv_rhs => rw [← he, ← Measure.map_id (μ := volume.restrict (Ioo (-Real.pi) Real.pi))]
  rw [Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
    Measure.map_map hm (by fun_prop)]
  unfold zernikeAnnulusProductMeasure
  dsimp only [ProductMeasureInput.ofSFinite]
  congr 1
  funext v
  change zernikeAnnulusCoordinates ⟨q,ne_of_lt q.property.2⟩ _ =
    e (safeAreaChart t ((v.1 : ℝ),v.2))
  have hd : 0 < 1-(v.1 : ℝ)/(t : ℝ) := by
    have := (div_lt_one (lt_trans zero_lt_one t.property)).mpr
      (lt_of_le_of_lt v.1.property.2 t.property)
    linarith
  rw [safeAreaChart_eq t _ hd]
  rfl

/-- The unweighted annular polar measure equals planar Lebesgue measure on the open annulus
(Papadopoulos–Gutleb–Slevinsky–Olver, Section 4). -/
theorem zernikeAnnulusMeasure_zero_zero_eq_volume {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ 0 0 =
      volume.restrict {v : Fin 2 → ℝ | q < v 0^2+v 1^2 ∧ v 0^2+v 1^2 < 1} := by
  let e : (ℝ × ℝ) ≃ᵐ (Fin 2 → ℝ) := MeasurableEquiv.finTwoArrow.symm
  let t : Ioi (1 : ℝ) := ⟨Polynomial.annulusParameter ⟨q,ne_of_lt hq.2⟩,
    Polynomial.one_lt_annulusParameter hq⟩
  have he := (volume_preserving_finTwoArrow ℝ).symm
  have hset : MeasurableSet {v : Fin 2 → ℝ | q < v 0^2+v 1^2 ∧ v 0^2+v 1^2 < 1} := by
    have hc : Continuous (fun v : Fin 2 → ℝ ↦ v 0^2+v 1^2) := by fun_prop
    exact (isOpen_lt continuous_const hc).measurableSet.inter
      (isOpen_lt hc continuous_const).measurableSet
  have hm := (he.restrict_preimage hset).map_eq
  have h := congrArg (Measure.map e)
    (safeArea_map_measure t)
  rw [Measure.map_smul _ e.measurable.aemeasurable,
    Measure.map_map e.measurable (measurable_safeAreaChart t)] at h
  have hs : Polynomial.semiclassicalJacobiMeasure ⟨2, by norm_num⟩ 0 0 0 =
      volume.restrict (Ioo (0 : ℝ) 1) := by
    have hw : Polynomial.semiclassicalJacobiWeight ⟨2,by norm_num⟩ 0 0 0 = 1 := by
      ext x
      simp [Polynomial.semiclassicalJacobiWeight_apply]
    change openIntervalWeightMeasure 0 1 _ = _
    rw [hw]
    simp only [openIntervalWeightMeasure, ContinuousMap.one_apply, ENNReal.coe_one]
    change Measure.map Subtype.val (volume.withDensity 1) = _
    rw [withDensity_one]
    exact map_comap_subtype_coe measurableSet_Ioo volume
  rw [zernikeAnnulusMeasure, safeArea_product_measure ⟨q,hq⟩, hs, Measure.prod_restrict]
  simp only [zero_add, add_zero, Real.rpow_one]
  rw [mul_comm (1/2 : ℝ), one_div, ← div_eq_mul_inv]
  rw [← Measure.volume_eq_prod, h]
  convert hm using 1
  simp [e, t, Polynomial.annulusParameter]
end
end MvPolynomial
