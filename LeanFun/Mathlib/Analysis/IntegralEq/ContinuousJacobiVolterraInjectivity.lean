/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousJacobiVolterra
public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousVolterraPrimitive
public import LeanFun.Mathlib.Analysis.IntegralEq.JacobiLocalIntegrability
public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraACUniqueness
@[expose] public noncomputable section
/-! # First-kind uniqueness in the weighted Jacobi realization

Compact interval tests turn a zero weak output into a zero physical Volterra
primitive. Local integrability and a countable interval cover then give
injectivity without imposing unweighted global integrability.
Reference: Linz (1985), first-kind Volterra uniqueness; Gutleb's thesis, §2.7.
-/

open MeasureTheory Polynomial Set
open scoped ENNReal InnerProductSpace
namespace Real
local notation "μ" => unitJacobiMeasure 1 0
local notation "ν" => volume.restrict (Icc (0 : ℝ) 1)
/-- A zero weighted output gives a zero physical primitive on every interior interval. -/
private theorem volterraIntegral_eq_zero_of_jacobiVolterraL2Operator_eq_zero_integral
    (K : (Fin 2 → ℝ) → ℝ) (hK : ContinuousOn K volterraTriangle) {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ z ∈ Real.volterraTriangle, |K z| ≤ M)
    (f : Lp ℝ 2 μ) (hz : jacobiVolterraL2Operator hK hM hbnd f = 0)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ x ∈ Icc 0 b, (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, K ![x,y] * f y) x = 0 := by
  let fc : ℝ → ℝ := (Icc (0 : ℝ) b).indicator f
  have hfi : Integrable fc volume :=
    (integrableOn_coe_jacobiOneZeroLp f hb1).integrable_indicator measurableSet_Icc
  have hfc : f =ᵐ[volume.restrict (Icc (0 : ℝ) b)] fc := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (indicator_of_mem hx _).symm
  have hv (x : ℝ) (hx : x ∈ Icc 0 b) :
      (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, K ![x,y] * f y) x = (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, K ![x,y] * fc y) x :=
    by
      have hxi : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hb1.le⟩
      have he := volterraIntegral_congr_ae_on K hx hfc
        (intervalIntegrable_continuousVolterra_mul_row hK ⟨x,hxi⟩
          (intervalIntegrable_of_integrableOn_Icc
            (integrableOn_coe_jacobiOneZeroLp f hb1) hx))
        (intervalIntegrable_continuousVolterra_mul hK hfi hxi)
      simpa only [volterraIntegral_ofKernel] using he
  dsimp only at hv
  let q : ℝ → ℝ := fun s ↦ (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, K ![x,y] * fc y) (1-s)
  let T := Icc (1-b) (1 : ℝ)
  have hprimitive : ContinuousOn
      (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, K ![x,y] * fc y) (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : Icc (0 : ℝ) 1 ↦
      ∫ y in (0 : ℝ)..(x : ℝ), K ![(x : ℝ),y] * fc y)
    simpa only [VolterraIntegralInput.ofContinuousKernel, volterraIntegral_ofKernel] using
      continuous_volterraIntegral_of_integrable hK hfi
  have hqc : ContinuousOn q T :=
    hprimitive.comp (by fun_prop)
      (fun s hs ↦ ⟨by linarith [hs.2],by linarith [hs.1]⟩)
  let G := T.indicator q
  let := isFiniteMeasure_unitJacobiMeasure (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := T) hqc
  have hGm : Measurable G := by
    have heq : G = T.piecewise q (fun _ ↦ (0 : ℝ)) := by
      funext x
      by_cases hx : x ∈ T <;> simp [G, hx]
    rw [heq]
    exact hqc.measurable_piecewise continuous_const.continuousOn measurableSet_Icc
  have hG : MemLp G 2 μ := by
    apply MemLp.of_bound hGm.aestronglyMeasurable |C|
    apply Filter.Eventually.of_forall
    intro s
    by_cases hs : s ∈ T
    · exact (congrArg (fun t : ℝ ↦ ‖t‖) (indicator_of_mem hs q)).trans_le
        ((hC s hs).trans (le_abs_self C))
    · exact (congrArg (fun t : ℝ ↦ ‖t‖) (indicator_of_notMem hs q)).trans_le
        (by simpa only [norm_zero] using abs_nonneg C)
  let g := hG.toLp G
  have hg : g =ᵐ[ν] G := ae_unitJacobiMeasure_one_zero_iff.mp hG.coeFn_toLp
  have hp : (fun s ↦ g s * (fun x : ℝ ↦ ∫ y in (0 : ℝ)..x, K ![x,y] * f y) (1-s)) =ᵐ[ν]
      T.indicator (fun s ↦ q s ^ 2) := by
    filter_upwards [hg] with s hs
    rw [hs]
    by_cases ht : s ∈ T
    · rw [indicator_of_mem ht, show G s = q s from indicator_of_mem ht q]
      rw [hv (1-s) ⟨by linarith [ht.2],by linarith [ht.1]⟩]
      change q s*q s = q s^2
      ring
    · simp only [G, indicator_of_notMem ht, zero_mul]
  have hi : (∫ s in T, q s ^ 2) = 0 := by
    have he := inner_jacobiVolterraL2Operator hK hM hbnd f g
    simp only [VolterraIntegralInput.ofJacobiOneZeroLp,
      VolterraIntegralInput.ofContinuousKernel, volterraIntegral_ofKernel] at he
    rw [integral_subtype_comap measurableSet_Ioo
      (fun s : ℝ ↦ g s * ∫ y in (0 : ℝ)..(1-s), K ![1-s,y] * f y),
      ← integral_Icc_eq_integral_Ioo] at he
    rw [hz, inner_zero_right, integral_congr_ae hp,
      integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (show T ⊆ Icc (0 : ℝ) 1 from
        fun s hs ↦ ⟨by linarith [hs.1],hs.2⟩)] at he
    linarith
  have hqa : (fun s ↦ q s^2) =ᵐ[volume.restrict T] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (fun s ↦ sq_nonneg (q s)))
      ((hqc.pow 2).integrableOn_Icc)).mp hi
  have he := Measure.eqOn_Icc_of_ae_eq volume (show 1-b ≠ (1 : ℝ) by linarith) hqa
    (hqc.pow 2) continuous_const.continuousOn
  intro x hx
  dsimp only
  rw [hv x hx]
  have h := he (show 1-x ∈ Icc (1-b) (1 : ℝ) from ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  dsimp only [q, Pi.zero_apply] at h
  rw [sub_sub_cancel] at h
  exact sq_eq_zero_iff.mp h
end Real
namespace Real
local notation "μ" => unitJacobiMeasure 1 0
/-- A zero weighted output gives zero classical rows on each compact interior interval. -/
theorem volterraIntegral_eq_zero_of_jacobiVolterraL2Operator_eq_zero
    (K : (Fin 2 → ℝ) → ℝ) (hK : ContinuousOn K volterraTriangle) {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ z ∈ volterraTriangle, |K z| ≤ M)
    (f : Lp ℝ 2 μ) (hz : jacobiVolterraL2Operator hK hM hbnd f = 0)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ x : Icc (0 : ℝ) b, volterraIntegral
      (.ofJacobiOneZeroLp hK f ⟨x, x.property.1, x.property.2.trans_lt hb1⟩) = 0 := by
  intro x
  simpa only [VolterraIntegralInput.ofJacobiOneZeroLp,
    VolterraIntegralInput.ofContinuousKernel, volterraIntegral_ofKernel] using
    volterraIntegral_eq_zero_of_jacobiVolterraL2Operator_eq_zero_integral
      K hK hM hbnd f hz hb0 hb1 x x.property

/-- A nonvanishing regular kernel diagonal makes the weighted zero-output input zero. -/
theorem eq_zero_of_jacobiVolterraL2Operator_eq_zero
    (K : (Fin 2 → ℝ) → ℝ) (hK : ContinuousOn K volterraTriangle) {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ z ∈ Real.volterraTriangle, |K z| ≤ M)
    {C : ℝ}
    (hAC : ∀ x ∈ Icc (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval (fun y ↦ K ![x,y]) 0 x)
    (hder : ∀ x ∈ Icc (0 : ℝ) 1,
      ∃ g : IntegrableDerivative (fun t ↦ K ![x,t]) (volume.restrict (uIcc 0 x)),
        ∀ᵐ y ∂volume.restrict (uIcc 0 x), ‖g y‖ ≤ C*|K ![x,x]|)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, K ![x,x] ≠ 0)
    (f : Lp ℝ 2 μ) (hz : jacobiVolterraL2Operator hK hM hbnd f = 0) : f = 0 := by
  have hlocal (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
      (fun x ↦ f x) =ᵐ[volume.restrict (Icc 0 b)] 0 :=
    ae_eq_zero_of_integrableOn_volterraIntegral_eq_zero
      (integrableOn_coe_jacobiOneZeroLp f hb1)
      (fun x hx ↦ hAC x ⟨hx.1,hx.2.trans hb1.le⟩)
      (fun x hx ↦ hdiag x ⟨hx.1,hx.2.trans hb1.le⟩)
      (fun x hx ↦ hder x ⟨hx.1,hx.2.trans hb1.le⟩)
      (by
        intro x hx
        simpa only [VolterraIntegralInput.ofAbsolutelyContinuous,
          VolterraIntegralInput.ofJacobiOneZeroLp,
          VolterraIntegralInput.ofContinuousKernel, volterraIntegral_ofKernel] using
          volterraIntegral_eq_zero_of_jacobiVolterraL2Operator_eq_zero
            K hK hM hbnd f hz hb0 hb1 ⟨x,hx⟩)
  have hq (q : ℚ) : ∀ᵐ x ∂volume,
      0 < (q : ℝ) → (q : ℝ) < 1 → x ∈ Icc 0 (q : ℝ) → f x = 0 := by
    by_cases h0 : 0 < (q : ℝ)
    · by_cases h1 : (q : ℝ) < 1
      · have h := (ae_restrict_iff' measurableSet_Icc).mp (hlocal q h0 h1)
        filter_upwards [h] with x hx
        exact fun _ _ hmem ↦ hx hmem
      · exact Filter.Eventually.of_forall (fun x _ h ↦ (h1 h).elim)
    · exact Filter.Eventually.of_forall (fun x h ↦ (h0 h).elim)
  have hall : ∀ᵐ x ∂volume, ∀ q : ℚ,
      0 < (q : ℝ) → (q : ℝ) < 1 → x ∈ Icc 0 (q : ℝ) → f x = 0 :=
    ae_all_iff.mpr hq
  apply Lp.ext
  have hz' := ae_unitJacobiMeasure_one_zero_iff.mp (Lp.coeFn_zero ℝ 2 μ)
  apply ae_unitJacobiMeasure_one_zero_iff.mpr
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Icc,
    ((volume.restrict (Icc (0 : ℝ) 1)).ae_ne 1), hz'] with x hx hxi hx1 hz'
  obtain ⟨q,hxq,hq1⟩ := exists_rat_btwn (lt_of_le_of_ne hxi.2 hx1)
  rw [hz']
  exact hx q (by linarith [hxi.1]) hq1 ⟨hxi.1,hxq.le⟩
/-- The weighted first-kind Volterra realization is injective for a nonvanishing diagonal. -/
theorem injective_jacobiVolterraL2Operator
    (K : (Fin 2 → ℝ) → ℝ) (hK : ContinuousOn K volterraTriangle) {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ z ∈ Real.volterraTriangle, |K z| ≤ M)
    {C : ℝ}
    (hAC : ∀ x ∈ Icc (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval (fun y ↦ K ![x,y]) 0 x)
    (hder : ∀ x ∈ Icc (0 : ℝ) 1,
      ∃ g : IntegrableDerivative (fun t ↦ K ![x,t]) (volume.restrict (uIcc 0 x)),
        ∀ᵐ y ∂volume.restrict (uIcc 0 x), ‖g y‖ ≤ C*|K ![x,x]|)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, K ![x,x] ≠ 0) :
    Function.Injective (jacobiVolterraL2Operator hK hM hbnd) := by
  intro f g h
  apply sub_eq_zero.mp
  apply eq_zero_of_jacobiVolterraL2Operator_eq_zero K hK hM hbnd hAC hder hdiag
  rw [map_sub, h, sub_self]
end Real
