/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.CriticalL2
public import LeanFun.Mathlib.Analysis.IntegralEq.WeakKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Endpoint tests for power-law operators

Separated intervals approaching an endpoint test same-space L² boundedness.
The scaling exponent is `α + λ + 1/2`. This is an elementary localized
Cauchy–Schwarz test for the weighted power-law operator of
Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

public section
open MeasureTheory Set Polynomial Filter
open scoped ENNReal NNReal InnerProductSpace Topology
namespace Real

attribute [local instance] Measure.Subtype.measureSpace

abbrev PowerLawWeakRealization (α lam : ℝ) :=
  {T : Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam) //
    ∀ f g : Lp ℝ 2 (gegenbauerMeasure lam),
      Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α lam) ∧
      ⟪g,T f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam}

theorem PowerLawWeakRealization.spec {α lam : ℝ} (T : PowerLawWeakRealization α lam)
    (f g : Lp ℝ 2 (gegenbauerMeasure lam)) :
    Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α lam) ∧
    ⟪g,T.val f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam := T.property f g

private theorem gegenbauerMeasure_endpoint_interval_lower {lam δ a b : ℝ}
    (hlam : -(1/2) < lam) (hlam1 : lam ≤ 1/2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 1-δ ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (2*δ)^(lam-1/2)*(b-a) ≤ (gegenbauerMeasure lam).real (Ioo a b) := by
  let := isFiniteMeasure_gegenbauerMeasure hlam
  have hsub : Ioo a b ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨w,hw,he,_,hμ⟩ := exists_subtypeNonnegativeDensity_extension
    measurableSet_Ioo (gegenbauerWeight lam) (gegenbauerWeight lam).continuous.measurable
  have hmeasure : gegenbauerMeasure lam = volume.withDensity (fun x ↦ (w x : ℝ≥0∞)) := hμ volume
  have hbound (x : ℝ) (hx : x ∈ Ioo a b) : (2*δ)^(lam-1/2) ≤ (w x : ℝ) := by
    rw [he ⟨x,hsub hx⟩,gegenbauerWeight_apply]
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hx1 : x < 1 := by linarith [hx.2]
    apply rpow_le_rpow_of_nonpos (by nlinarith : 0 < 1-x^2) _ (by linarith)
    nlinarith [sq_nonneg (x-1),hx.1]
  have hh : ENNReal.ofReal ((2*δ)^(lam-1/2)*(b-a)) ≤ gegenbauerMeasure lam (Ioo a b) := by
    rw [hmeasure,withDensity_apply _ measurableSet_Ioo]
    calc
      _ = ∫⁻ _ in Ioo a b, ENNReal.ofReal ((2*δ)^(lam-1/2)) := by
        rw [lintegral_const]
        simp only [Measure.restrict_apply_univ,Real.volume_Ioo]
        rw [ENNReal.ofReal_mul (rpow_nonneg (by positivity : 0 ≤ 2*δ) _)]
      _ ≤ _ := setLIntegral_mono' measurableSet_Ioo (fun x hx ↦ by
        simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hbound x hx))
  have ht := ENNReal.toReal_mono (measure_ne_top (gegenbauerMeasure lam) _) hh
  rw [ENNReal.toReal_ofReal (mul_nonneg (rpow_nonneg (by positivity) _) (sub_nonneg.mpr hab.le))] at ht
  exact ht

theorem gegenbauerMeasure_endpoint_interval_lowerOn (lam : Ioc (-(1/2) : ℝ) (1/2))
    (δ : Ioc (0 : ℝ) 1) (a b : Icc (1-δ.val) (1 : ℝ)) (hab : a.val < b.val) :
    (2*δ.val)^(lam.val-1/2)*(b.val-a.val) ≤ (gegenbauerMeasure lam.val).real (Ioo a.val b.val) :=
  gegenbauerMeasure_endpoint_interval_lower lam.property.1 lam.property.2 δ.property.1 δ.property.2
    a.property.1 hab b.property.2

theorem exists_powerLawKernel_offDiagonal_density (α : ℝ) :
    ∃ w : ℝ × ℝ → ℝ≥0, Measurable w ∧
      (∀ z : {z : ℝ × ℝ // z.1 ≠ z.2}, (w z.val : ℝ) = |z.val.1-z.val.2|^α) ∧
      ∀ tau lam : ℝ, twoWeightPowerLawKernelMeasure α tau lam =
        ((gegenbauerMeasure tau).prod (gegenbauerMeasure lam)).withDensity
          (fun z ↦ (w z : ℝ≥0∞)) := by
  let D := {z : ℝ × ℝ | z.1 ≠ z.2}
  have hD : MeasurableSet D := (measurableSet_eq_fun measurable_fst measurable_snd).compl
  let density (z : D) : ℝ≥0 := ⟨|z.val.1-z.val.2|^α,rpow_nonneg (abs_nonneg _) _⟩
  have hd : Measurable density := by
    apply measurable_coe_nnreal_real_iff.mp
    change Measurable (fun z : D ↦ |z.val.1-z.val.2|^α)
    fun_prop
  obtain ⟨w,hw,he,_,_⟩ := exists_subtypeNonnegativeDensity_extension hD density hd
  refine ⟨w,hw,fun z ↦ congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) (he z),?_⟩
  intro tau lam
  obtain ⟨K,_,hKe,_,hμ⟩ := exists_powerLawKernel_density α
  rw [hμ]
  apply withDensity_congr_ae
  filter_upwards [ae_mem_powerLawKernelDomain tau lam] with z hz
  have hh : K z = w z := by
    apply NNReal.eq
    exact (hKe ⟨z,hz⟩).trans (congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) (he ⟨z,hz.2.2⟩)).symm
  rw [hh]

theorem exists_powerLawWeakKernel (α lam : ℝ)
    (T : Lp ℝ 2 (gegenbauerMeasure lam) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam))
    (hT : ∀ f g : Lp ℝ 2 (gegenbauerMeasure lam),
      Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α lam) ∧
      ⟪g,T f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α lam) :
    ∃ K : L2WeakKernel (gegenbauerMeasure lam), K.operator = T ∧
      ∀ z : {z : ℝ × ℝ // z.1 ≠ z.2}, K.kernel z.val = |z.val.1-z.val.2|^α := by
  let : SFinite (gegenbauerMeasure lam) := sFinite_gegenbauerMeasure _
  obtain ⟨w,hw,he,hμ⟩ := exists_powerLawKernel_offDiagonal_density α
  have hm : powerLawKernelMeasure α lam =
      ((gegenbauerMeasure lam).prod (gegenbauerMeasure lam)).withDensity
        (fun z ↦ (w z : ℝ≥0∞)) := hμ lam lam
  have hpair (f g : Lp ℝ 2 (gegenbauerMeasure lam)) :
      Integrable (fun z ↦ (w z : ℝ)*(g z.1*f z.2))
        ((gegenbauerMeasure lam).prod (gegenbauerMeasure lam)) ∧
      ⟪g,T f⟫_ℝ = ∫ z, (w z : ℝ)*(g z.1*f z.2)
        ∂(gegenbauerMeasure lam).prod (gegenbauerMeasure lam) := by
    have h := hT f g
    constructor
    · rw [hm,integrable_withDensity_iff hw.coe_nnreal_ennreal (by simp)] at h
      simpa only [ENNReal.coe_toReal,smul_eq_mul,mul_comm] using h.1
    · rw [hm,integral_withDensity_eq_integral_toReal_smul hw.coe_nnreal_ennreal (by simp)] at h
      simpa only [ENNReal.coe_toReal,smul_eq_mul] using h.2
  exact ⟨L2WeakKernel.ofSFinite (fun z ↦ (w z : ℝ)) T
    (fun f g ↦ (hpair f g).1) (fun f g ↦ (hpair f g).2),rfl,he⟩

private theorem powerLaw_rectangle_lower_le_norm_of_kernel {α lam δ : ℝ}
    (hlam : -(1/2) < lam) (hα : α ≤ 0) (hδ : 0 < δ)
    (K : L2WeakKernel (gegenbauerMeasure lam))
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ/4 ≤ |x-y| ∧ |x-y| ≤ δ)
    (hk : ∀ x ∈ A, ∀ y ∈ B, K.kernel (x,y) = |x-y|^α)
    (hposA : 0 < (gegenbauerMeasure lam).real A)
    (hposB : 0 < (gegenbauerMeasure lam).real B) :
    δ^α * sqrt ((gegenbauerMeasure lam).real A) * sqrt ((gegenbauerMeasure lam).real B) ≤ ‖K.operator‖ := by
  let μ := gegenbauerMeasure lam
  let := isFiniteMeasure_gegenbauerMeasure hlam
  have hki := K.integrableOn_rectangle hA hB
  have hl : δ^α * (μ.real A * μ.real B) ≤ ∫ z in A ×ˢ B, K.kernel z ∂μ.prod μ := by
    have hc : (∫ _ in A ×ˢ B, δ^α ∂μ.prod μ) = δ^α*(μ.real A*μ.real B) := by
      simp only [integral_const,Measure.real,Measure.restrict_apply_univ,
        Measure.prod_prod,ENNReal.toReal_mul,smul_eq_mul]
      ring
    rw [← hc]
    apply integral_mono_ae (integrable_const _) hki
    filter_upwards [ae_restrict_mem (hA.prod hB)] with z hz
    rw [hk z.1 hz.1 z.2 hz.2]
    exact rpow_le_rpow_of_nonpos
      ((div_pos hδ (by norm_num : (0 : ℝ) < 4)).trans_le (hsep z.1 hz.1 z.2 hz.2).1)
      (hsep z.1 hz.1 z.2 hz.2).2 hα
  have hu := K.rectangle_bound hA hB |>.2
  have hab : 0 < sqrt (μ.real A)*sqrt (μ.real B) := mul_pos (sqrt_pos.mpr hposA) (sqrt_pos.mpr hposB)
  have hb := hl.trans ((le_abs_self _).trans hu)
  apply (mul_le_mul_iff_left₀ hab).mp
  change (δ^α * sqrt (μ.real A) * sqrt (μ.real B)) *
    (sqrt (μ.real A)*sqrt (μ.real B)) ≤ _
  calc
    _ = δ^α * ((sqrt (μ.real A))^2*(sqrt (μ.real B))^2) := by ring
    _ = δ^α * (μ.real A*μ.real B) := by rw [sq_sqrt hposA.le, sq_sqrt hposB.le]
    _ ≤ _ := by simpa [mul_assoc] using hb

theorem powerLaw_rectangle_lower_le_norm_of_agreesOn (α : Iic (0 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (δ : Ioi (0 : ℝ))
    (K : L2WeakKernel (gegenbauerMeasure lam.val))
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ.val/4 ≤ |x-y| ∧ |x-y| ≤ δ.val)
    (hk : ∀ z : {z : ℝ × ℝ // z.1 ∈ A ∧ z.2 ∈ B ∧ z.1 ≠ z.2},
      K.kernel z.val = |z.val.1-z.val.2|^α.val)
    (hApos : 0 < (gegenbauerMeasure lam.val).real A)
    (hBpos : 0 < (gegenbauerMeasure lam.val).real B) :
    δ.val^α.val * sqrt ((gegenbauerMeasure lam.val).real A)*sqrt ((gegenbauerMeasure lam.val).real B) ≤ ‖K.operator‖ := by
  apply powerLaw_rectangle_lower_le_norm_of_kernel lam.property α.property δ.property K hA hB hsep _ hApos hBpos
  intro x hx y hy
  exact hk ⟨(x,y),hx,hy,sub_ne_zero.mp (abs_pos.mp
    ((div_pos δ.property (by norm_num : (0 : ℝ) < 4)).trans_le (hsep x hx y hy).1))⟩

private theorem powerLaw_endpoint_scaling_le_norm_of_kernel {α lam δ : ℝ}
    (hlam : -(1/2) < lam) (hlam1 : lam ≤ 1/2) (hα : α ≤ 0)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (K : L2WeakKernel (gegenbauerMeasure lam))
    (hk : ∀ x ∈ Ioo (1-δ) 1, ∀ y ∈ Ioo (1-δ) 1, x ≠ y → K.kernel (x,y) = |x-y|^α) :
    (2^(lam-1/2)/4)*δ^(α+lam+1/2) ≤ ‖K.operator‖ := by
  let A := Ioo (1-δ) (1-3*δ/4)
  let B := Ioo (1-δ/2) (1-δ/4)
  let L := (2*δ)^(lam-1/2)*(δ/4)
  have hL : 0 < L := by dsimp [L]; positivity
  have hA : L ≤ (gegenbauerMeasure lam).real A := by
    have hh := gegenbauerMeasure_endpoint_interval_lowerOn ⟨lam,hlam,hlam1⟩ ⟨δ,hδ,hδ1⟩
      ⟨1-δ,by constructor <;> linarith⟩ ⟨1-3*δ/4,by constructor <;> linarith⟩
      (by change 1-δ < 1-3*δ/4; linarith)
    convert hh using 1; dsimp [L, A]; ring
  have hB : L ≤ (gegenbauerMeasure lam).real B := by
    have hh := gegenbauerMeasure_endpoint_interval_lowerOn ⟨lam,hlam,hlam1⟩ ⟨δ,hδ,hδ1⟩
      ⟨1-δ/2,by constructor <;> linarith⟩ ⟨1-δ/4,by constructor <;> linarith⟩
      (by change 1-δ/2 < 1-δ/4; linarith)
    convert hh using 1; dsimp [L, B]; ring
  have hbound := powerLaw_rectangle_lower_le_norm_of_agreesOn ⟨α,hα⟩ ⟨lam,hlam⟩ ⟨δ,hδ⟩ K
    (A := A) (B := B) measurableSet_Ioo measurableSet_Ioo (by
      intro x hx y hy
      dsimp [A, B] at hx hy
      rw [abs_of_neg (by linarith [hx.2, hy.1] : x-y < 0)]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
    (by
      intro z
      have hx := z.property.1
      have hy := z.property.2.1
      apply hk z.val.1 ⟨hx.1,by dsimp [A] at hx; linarith [hx.2]⟩ z.val.2
        (by dsimp [B] at hy; constructor <;> linarith [hy.1,hy.2]) z.property.2.2)
    (hL.trans_le hA) (hL.trans_le hB)
  have hs : L ≤ sqrt ((gegenbauerMeasure lam).real A)*sqrt ((gegenbauerMeasure lam).real B) := by
    calc
      L = sqrt (L*L) := (sqrt_mul_self hL.le).symm
      _ ≤ sqrt ((gegenbauerMeasure lam).real A * (gegenbauerMeasure lam).real B) :=
        sqrt_le_sqrt (mul_le_mul hA hB hL.le (hL.le.trans hA))
      _ = _ := sqrt_mul (hL.le.trans hA) _
  have he : δ^α * L = (2^(lam-1/2)/4)*δ^(α+lam+1/2) := by
    dsimp [L]
    rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.le]
    have he : α+lam+1/2 = α+(lam-1/2)+1 := by ring
    rw [he, rpow_add hδ, rpow_add hδ, rpow_one]
    ring
  rw [← he]
  exact (mul_le_mul_of_nonneg_left hs (rpow_nonneg hδ.le _)).trans (by simpa [mul_assoc] using hbound)

theorem powerLaw_endpoint_scaling_le_norm_of_agreesOn (α : Iic (0 : ℝ))
    (lam : Ioc (-(1/2) : ℝ) (1/2)) (δ : Ioc (0 : ℝ) 1)
    (K : L2WeakKernel (gegenbauerMeasure lam.val))
    (hk : ∀ z : {z : ℝ × ℝ // z.1 ∈ Ioo (1-δ.val) 1 ∧
        z.2 ∈ Ioo (1-δ.val) 1 ∧ z.1 ≠ z.2},
      K.kernel z.val = |z.val.1-z.val.2|^α.val) :
    (2^(lam.val-1/2)/4)*δ.val^(α.val+lam.val+1/2) ≤ ‖K.operator‖ := by
  exact powerLaw_endpoint_scaling_le_norm_of_kernel lam.property.1 lam.property.2 α.property δ.property.1 δ.property.2 K
    (fun x hx y hy hne ↦ hk ⟨(x,y),hx,hy,hne⟩)

theorem powerLaw_rectangle_lower_le_normOn (α : Iic (0 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (δ : Ioi (0 : ℝ)) (T : PowerLawWeakRealization α.val lam.val)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ.val/4 ≤ |x-y| ∧ |x-y| ≤ δ.val)
    (hApos : 0 < (gegenbauerMeasure lam.val).real A)
    (hBpos : 0 < (gegenbauerMeasure lam.val).real B) :
    δ.val^α.val * sqrt ((gegenbauerMeasure lam.val).real A)*sqrt ((gegenbauerMeasure lam.val).real B) ≤ ‖T.val‖ := by
  obtain ⟨K,hK,he⟩ := exists_powerLawWeakKernel α.val lam.val T.val T.property
  rw [← hK]
  exact powerLaw_rectangle_lower_le_norm_of_agreesOn α lam δ K hA hB hsep
    (fun z ↦ he ⟨z.val,z.property.2.2⟩) hApos hBpos

theorem powerLaw_endpoint_scaling_le_normOn (α : Iic (0 : ℝ))
    (lam : Ioc (-(1/2) : ℝ) (1/2)) (δ : Ioc (0 : ℝ) 1)
    (T : PowerLawWeakRealization α.val lam.val) :
    (2^(lam.val-1/2)/4)*δ.val^(α.val+lam.val+1/2) ≤ ‖T.val‖ := by
  obtain ⟨K,hK,he⟩ := exists_powerLawWeakKernel α.val lam.val T.val T.property
  rw [← hK]
  exact powerLaw_endpoint_scaling_le_norm_of_agreesOn α lam δ K
    (fun z ↦ he ⟨z.val,z.property.2.2⟩)

theorem not_exists_powerLawL2Operator_below_endpointOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (hs : α.val+lam.val < -(1/2)) :
    ¬Nonempty (PowerLawWeakRealization α.val lam.val) := by
  rintro ⟨T⟩
  obtain ⟨K,hK,hKe⟩ := exists_powerLawWeakKernel α.val lam.val T.val T.property
  have ht := Filter.Tendsto.const_mul_atTop
    (by positivity : 0 < (2 : ℝ)^(lam.val-1/2)/4)
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : α.val+lam.val+1/2 < 0))
  have hev := ht.eventually (eventually_gt_atTop ‖T.val‖)
  have hd : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ 1 :=
    nhdsWithin_le_nhds (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨δ,hgt,hle,hpos⟩ := (hev.and (hd.and self_mem_nhdsWithin)).exists
  have hl := powerLaw_endpoint_scaling_le_norm_of_agreesOn
    ⟨α.val,by change α.val ≤ 0; linarith [show -(1/2 : ℝ) < lam.val from lam.property]⟩
    ⟨lam.val,lam.property,by change lam.val ≤ 1/2; linarith [show (-1 : ℝ) < α.val from α.property]⟩
    ⟨δ,hpos,hle⟩ K (fun z ↦ hKe ⟨z.val,z.property.2.2⟩)
  rw [hK] at hl
  exact (not_lt_of_ge hl) hgt

theorem exists_powerLawL2Operator_iffOn (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ)) :
    (∃ T : Lp ℝ 2 (gegenbauerMeasure lam.val) →L[ℝ] Lp ℝ 2 (gegenbauerMeasure lam.val),
      (∀ f g : Lp ℝ 2 (gegenbauerMeasure lam.val),
        Integrable (fun z : ℝ × ℝ ↦ g z.1*f z.2) (powerLawKernelMeasure α.val lam.val)) ∧
      ∀ f g, ⟪g,T f⟫_ℝ = ∫ z : ℝ × ℝ, g z.1*f z.2 ∂powerLawKernelMeasure α.val lam.val) ↔
      -(1/2) ≤ α.val+lam.val := by
  constructor
  · rintro ⟨T,hi,he⟩
    by_contra hnot
    exact not_exists_powerLawL2Operator_below_endpointOn α lam (lt_of_not_ge hnot)
      ⟨⟨T,fun f g ↦ ⟨hi f g,he f g⟩⟩⟩
  · intro hs
    obtain ⟨M,T,_,_,hT⟩ := exists_powerLawL2Operator_of_le_endpointOn α lam hs
    exact ⟨T,fun f g ↦ (hT f g).1,fun f g ↦ (hT f g).2⟩

end Real
