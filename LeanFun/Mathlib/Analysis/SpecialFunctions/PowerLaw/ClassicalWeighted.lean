/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import Mathlib.Topology.Algebra.Polynomial
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerIntegrability
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerEndpoint
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerSymmetric
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerFirstMode
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerHypergeometric
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.ClassicalAnalytic
import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.ClassicalEuler
import LeanFun.Mathlib.MeasureTheory.Integral.SquaredRadius
/-! # Classical weighted power-law inputs and Gauss evaluations
Weighted integrability is bundled before evaluation. The endpoint domain uses
the combined exponent; interior inputs retain all lambda > -1/2, including zero.
References: Gutleb--Carrillo--Olver, arXiv:2011.00045, Section2;
DLMF5.12.1 and15.6.1.
-/
@[expose] public noncomputable section
open MeasureTheory Set Polynomial Filter
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
namespace Real
/-- Interior kernel integrability on its punctured domain, including parameter zero. -/
theorem integrable_powerLaw_gegenbauer_kernel (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    Integrable (fun y : PowerLawDomain x.val ↦ |x.val-y.val|^α.val *
      (gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ))
      (Measure.comap Subtype.val volume) := by
  let K : ℝ → ℝ := fun y ↦ if y ≠ x.val then |x.val-y|^α.val else 0
  let W : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo (-1 : ℝ) 1 then
    (gegenbauerWeight lam.val ⟨y,h⟩ : ℝ) else 0
  have hK : IntervalIntegrable K volume (-1) 1 := by
    have hi : IntegrableOn K {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x.val} volume := by
      apply (integrableOn_iff_comap_subtypeVal (f := K) (μ := volume)
        (measurableSet_powerLawDomain x.val)).mpr
      have h := (PowerLawInput.one α ⟨x.val,Ioo_subset_Icc_self x.property⟩).property
      apply h.congr
      filter_upwards [] with y
      change |x.val-y.val|^α.val * 1 = K y.val
      simp only [K,ite_eq_left y.property.2,mul_one]
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    apply (integrableOn_congr_set_ae (show {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x.val} =ᵐ[volume]
      Ioo (-1 : ℝ) 1 from ?_)).mp hi
    filter_upwards [volume.ae_ne x.val] with y hy
    exact propext ⟨And.left,fun h ↦ ⟨h,hy⟩⟩
  have hlam : -(1/2 : ℝ) < lam.val := lam.property
  have hW : IntervalIntegrable W volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    apply (integrableOn_iff_comap_subtypeVal (f := W) (μ := volume) measurableSet_Ioo).mpr
    have h := integrable_jacobiWeight (α := lam.val-1/2) (β := lam.val-1/2)
      (by linarith [hlam]) (by linarith [hlam])
    simp only [Measure.Subtype.volume_def] at h
    apply h.congr
    filter_upwards [] with y
    simp only [Function.comp_def,W,dite_eq_left y.property]
    rfl
  have hKcont {y : ℝ} (hy : y ≠ x.val) : ContinuousAt K y := by
    have hraw : ContinuousAt (fun t : ℝ ↦ |x.val-t|^α.val) y :=
      ((continuousAt_const.sub continuousAt_id).abs).rpow_const
        (Or.inl (abs_ne_zero.mpr (sub_ne_zero.mpr hy.symm)))
    apply hraw.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy] with t ht
    change (if t ≠ x.val then _ else _) = _
    exact ite_eq_left (show t ≠ x.val from ht)
  have hWcont {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) : ContinuousAt W y := by
    dsimp only [W]
    have hc : ContinuousOn (fun t : ℝ ↦ if h : t ∈ Ioo (-1 : ℝ) 1 then
        (gegenbauerWeight lam.val ⟨t,h⟩ : ℝ) else 0) (Ioo (-1 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have he : (fun t : Ioo (-1 : ℝ) 1 ↦ if h : t.val ∈ Ioo (-1 : ℝ) 1 then
          (gegenbauerWeight lam.val ⟨t.val,h⟩ : ℝ) else 0) =
          (fun t : Ioo (-1 : ℝ) 1 ↦ (gegenbauerWeight lam.val t : ℝ)) := by
        funext t
        simp only [dite_eq_left t.property]
      change Continuous (fun t : Ioo (-1 : ℝ) 1 ↦ if h : t.val ∈ Ioo (-1 : ℝ) 1 then
        (gegenbauerWeight lam.val ⟨t.val,h⟩ : ℝ) else 0)
      rw [he]
      exact continuous_subtype_val.comp (gegenbauerWeight lam.val).continuous
    exact hc.continuousAt (isOpen_Ioo.mem_nhds hy)
  let a : ℝ := (x.val-1)/2
  let b : ℝ := (x.val+1)/2
  have ha : -1 < a ∧ a < x.val := by dsimp [a]; constructor <;> linarith [x.property.1]
  have hb : x.val < b ∧ b < 1 := by dsimp [b]; constructor <;> linarith [x.property.2]
  have hab : a ≤ b := by linarith
  have hl : IntervalIntegrable (fun y ↦ K y * W y) volume (-1) a := by
    apply (hW.mono_set (by
      rw [uIcc_of_le ha.1.le,uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc le_rfl (by linarith))).continuousOn_mul
    apply continuousOn_of_forall_continuousAt
    intro y hy
    rw [uIcc_of_le ha.1.le] at hy
    exact hKcont (by linarith [hy.2])
  have hm : IntervalIntegrable (fun y ↦ K y * W y) volume a b := by
    apply (hK.mono_set (by
      rw [uIcc_of_le hab,uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc ha.1.le hb.2.le)).mul_continuousOn
    apply continuousOn_of_forall_continuousAt
    intro y hy
    rw [uIcc_of_le hab] at hy
    exact hWcont ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hr : IntervalIntegrable (fun y ↦ K y * W y) volume b 1 := by
    apply (hW.mono_set (by
      rw [uIcc_of_le hb.2.le,uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Icc_subset_Icc (by linarith) le_rfl)).continuousOn_mul
    apply continuousOn_of_forall_continuousAt
    intro y hy
    rw [uIcc_of_le hb.2.le] at hy
    exact hKcont (by linarith [hy.1])
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp
    ((hl.trans hm).trans hr)
  have hj := hi.mono_set (show {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ x.val} ⊆ Ioo (-1 : ℝ) 1 from fun _ h ↦ h.1)
  have hk := (integrableOn_iff_comap_subtypeVal (measurableSet_powerLawDomain x.val)).mp hj
  apply hk.congr
  filter_upwards [] with y
  simp only [Function.comp_def,K,W,ite_eq_left y.property.2,dite_eq_left y.property.1]

/-- The weighted continuous input is defined on the kernel's classical domain. -/
def PowerLawInput.gegenbauerContinuous (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (f : C(Icc (-1 : ℝ) 1, ℝ)) : PowerLawInput α.val x.val := by
  refine ⟨fun y ↦ (gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ) *
    f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩, ?_⟩
  have hi := integrable_powerLaw_gegenbauer_kernel α lam x
  have hc : Continuous (fun y : PowerLawDomain x.val ↦
      f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩) := by fun_prop
  have hb : ∀ᵐ y : PowerLawDomain x.val ∂Measure.comap Subtype.val volume,
      ‖f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩‖ ≤ ‖f‖ :=
    Eventually.of_forall (fun y ↦ ContinuousMap.norm_coe_le_norm f _)
  convert hi.mul_bdd hc.aestronglyMeasurable hb using 1
  funext y
  change |x.val-y.val|^α.val * ((gegenbauerWeight lam.val _ : ℝ)*_) =
    (|x.val-y.val|^α.val * (gegenbauerWeight lam.val _ : ℝ))*_
  ring

/-- Pointwise characterization of the weighted input. -/
theorem PowerLawInput.gegenbauerContinuous_apply (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) (y : PowerLawDomain x.val) :
    (PowerLawInput.gegenbauerContinuous α lam x f).val y =
      (gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ) *
        f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩ := rfl
end Real
namespace Real
/-- Endpoint data use the combined singularity exponent, without an unnecessary alpha bound. -/
abbrev PowerLawEndpointParameters := {p : ℝ × ℝ // -(1/2) < p.2 ∧ -(1/2) < p.1+p.2}
/-- At the right endpoint, multiplication adds the kernel exponent to the first
Jacobi exponent (DLMF 5.12.1). -/
theorem powerLaw_mul_gegenbauerWeight_one (α lam : ℝ) (y : Ioo (-1 : ℝ) 1) :
    |1-(y : ℝ)|^α * (gegenbauerWeight lam y : ℝ) =
      (jacobiWeight (α+(lam-1/2)) (lam-1/2) y : ℝ) := by
  change |1-(y : ℝ)|^α * (jacobiWeight (lam-1/2) (lam-1/2) y : ℝ) = _
  rw [jacobiWeight_apply, jacobiWeight_apply,
    abs_of_pos (by linarith [y.property.2] : 0 < 1-(y : ℝ)),
    rpow_add (by linarith [y.property.2] : 0 < 1-(y : ℝ))]
  ring

/-- The Gegenbauer input at the right endpoint. -/
def PowerLawInput.gegenbauerEndpoint (p : PowerLawEndpointParameters) : PowerLawInput p.val.1 1 := by
  refine ⟨fun y ↦ (gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ), ?_⟩
  let W : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo (-1 : ℝ) 1 then
    (jacobiWeight (p.val.1+(p.val.2-1/2)) (p.val.2-1/2) ⟨y,h⟩ : ℝ) else 0
  have hi : Integrable (fun y : Ioo (-1 : ℝ) 1 ↦ W y)
      (Measure.comap Subtype.val (volume : Measure ℝ)) := by
    change Integrable (fun y : Ioo (-1 : ℝ) 1 ↦ W y) volume
    convert integrable_jacobiWeight (show -1 < p.val.1+(p.val.2-1/2) by linarith [p.property.2])
        (show -1 < p.val.2-1/2 by linarith [p.property.1]) using 1
    funext y
    simp only [W, dite_eq_left y.property]
  have hs : {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ 1} = Ioo (-1 : ℝ) 1 := by
    ext y
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, ne_of_lt h.2⟩⟩
  have hj := (integrableOn_iff_comap_subtypeVal (f := W) (μ := volume) measurableSet_Ioo).mpr hi
  rw [← hs] at hj
  have hk := (integrableOn_iff_comap_subtypeVal (f := W) (μ := volume) (measurableSet_Ioo.inter (measurableSet_singleton (1 : ℝ)).compl)).mp hj
  apply hk.congr
  filter_upwards [] with y
  simp only [Function.comp_def, W, dite_eq_left y.property.1]
  exact (powerLaw_mul_gegenbauerWeight_one p.val.1 p.val.2 ⟨y.val,y.property.1⟩).symm
/-- The endpoint constructor is exactly the classical Gegenbauer density. -/
theorem PowerLawInput.gegenbauerEndpoint_apply (p : PowerLawEndpointParameters)
    (y : PowerLawDomain 1) :
    (PowerLawInput.gegenbauerEndpoint p).val y =
      (gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ) := rfl
/-- The endpoint formula uses only positive-argument Gamma values. -/
theorem powerLawIntegral_gegenbauerEndpoint (p : PowerLawEndpointParameters) :
    powerLawIntegral (.gegenbauerEndpoint p) =
      (2 : ℝ)^(p.val.1+2*p.val.2) *
        GammaOn (.ofPos (p.val.1+p.val.2+1/2) (by linarith [p.property.2])) *
        GammaOn (.ofPos (p.val.2+1/2) (by linarith [p.property.1])) /
        GammaOn (.ofPos (p.val.1+2*p.val.2+1) (by linarith [p.property.1,p.property.2])) := by
  calc
    _ = ∫ y : Ioo (-1 : ℝ) 1,
        (jacobiWeight (p.val.1+(p.val.2-1/2)) (p.val.2-1/2) y : ℝ) := by
      let W : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo (-1 : ℝ) 1 then
        (jacobiWeight (p.val.1+(p.val.2-1/2)) (p.val.2-1/2) ⟨y,h⟩ : ℝ) else 0
      have hs : {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ 1} = Ioo (-1 : ℝ) 1 := by
        ext y
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, ne_of_lt h.2⟩⟩
      calc
        _ = ∫ y : PowerLawDomain 1, W y ∂Measure.comap Subtype.val volume := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp only [PowerLawInput.gegenbauerEndpoint_apply, W, dite_eq_left y.property.1]
          exact powerLaw_mul_gegenbauerWeight_one p.val.1 p.val.2 ⟨y.val,y.property.1⟩
        _ = ∫ y in {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ y ≠ 1}, W y :=
          integral_subtype_comap (measurableSet_Ioo.inter (measurableSet_singleton (1 : ℝ)).compl) W
        _ = _ := by
          rw [hs, ← integral_subtype_comap measurableSet_Ioo W]
          apply integral_congr_ae
          filter_upwards [] with y
          simp only [W, dite_eq_left y.property]
    _ = _ := by
      rw [integral_jacobiWeight (by linarith [p.property.2])
        (by linarith [p.property.1])]
      simp only [GammaOn, GammaPoint.ofPos]
      rw [show p.val.1+(p.val.2-1/2)+(p.val.2-1/2)+1 = p.val.1+2*p.val.2 by ring,
        show p.val.1+(p.val.2-1/2)+1 = p.val.1+p.val.2+1/2 by ring,
        show p.val.2-1/2+1 = p.val.2+1/2 by ring,
        show p.val.1+(p.val.2-1/2)+(p.val.2-1/2)+2 = p.val.1+2*p.val.2+1 by ring]

end Real
namespace Real
/-- The constant weighted interior input. -/
def PowerLawInput.gegenbauerWeight (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) : PowerLawInput α.val x.val :=
  .gegenbauerContinuous α lam x 1
/-- The interior input is exactly the Gegenbauer density. -/
theorem PowerLawInput.gegenbauerWeight_apply (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (y : PowerLawDomain x.val) :
    (PowerLawInput.gegenbauerWeight α lam x).val y =
      (Polynomial.gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ) := by
  exact mul_one _
private theorem left_affine_integral (α : ℝ) (x : Ioo (-1 : ℝ) 1)
    (f : PowerLawLeftInput α ⟨x.val,x.property.1.le⟩) :
    powerLawLeft f = (x.val+1) * ∫ t : Ioo (0 : ℝ) 1,
      (x.val-((x.val+1)*t.val-1))^α *
        f.val ⟨(x.val+1)*t.val-1, by
          have hL : 0 < x.val+1 := by linarith [x.property.1]
          constructor
          · linarith [mul_pos hL t.property.1]
          · linarith [mul_lt_mul_of_pos_left t.property.2 hL]⟩
      ∂Measure.comap Subtype.val volume := by
  let F : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo (-1 : ℝ) x.val then
    (x.val-y)^α * f.val ⟨y,h⟩ else 0
  have he (y : Ioo (-1 : ℝ) x.val) : F y.val = (x.val-y.val)^α*f.val y := by
    simp only [F,dite_eq_left y.property]
  have hi : IntegrableOn F (Ioo (-1 : ℝ) x.val) volume := by
    apply (integrableOn_iff_comap_subtypeVal (f := F) (μ := volume) measurableSet_Ioo).mpr
    apply f.property.congr
    filter_upwards [] with y
    exact (he y).symm
  calc
    _ = ∫ y in (-1 : ℝ)..x.val, F y := by
      rw [intervalIntegral.integral_of_le x.property.1.le,integral_Ioc_eq_integral_Ioo,
        ← integral_subtype_comap measurableSet_Ioo F]
      apply integral_congr_ae
      filter_upwards [] with y
      exact (he y).symm
    _ = (x.val+1) * ∫ t in (0 : ℝ)..1, F ((x.val+1)*t-1) := by
      simpa only [smul_eq_mul,mul_zero,zero_sub,mul_one,add_sub_cancel_right]
        using (intervalIntegral.smul_integral_comp_mul_sub (E := ℝ) F
          (a := 0) (b := 1) (x.val+1) 1).symm
    _ = _ := by
      congr 1
      rw [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo,
        ← integral_subtype_comap measurableSet_Ioo (fun t ↦ F ((x.val+1)*t-1))]
      apply integral_congr_ae
      filter_upwards [] with t
      exact he ⟨(x.val+1)*t.val-1, by
        have hL : 0 < x.val+1 := by linarith [x.property.1]
        constructor
        · linarith [mul_pos hL t.property.1]
        · linarith [mul_lt_mul_of_pos_left t.property.2 hL]⟩
private theorem right_affine_integral (α : ℝ) (x : Ioo (-1 : ℝ) 1)
    (f : PowerLawRightInput α ⟨x.val,x.property.2.le⟩) :
    powerLawRight f = (1-x.val) * ∫ t : Ioo (0 : ℝ) 1,
      (1-(1-x.val)*t.val-x.val)^α *
        f.val ⟨1-(1-x.val)*t.val, by
          have hL : 0 < 1-x.val := by linarith [x.property.2]
          constructor
          · linarith [mul_lt_mul_of_pos_left t.property.2 hL]
          · linarith [mul_pos hL t.property.1]⟩
      ∂Measure.comap Subtype.val volume := by
  let F : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo x.val (1 : ℝ) then
    (y-x.val)^α * f.val ⟨y,h⟩ else 0
  have he (y : Ioo x.val (1 : ℝ)) : F y.val = (y.val-x.val)^α*f.val y := by
    simp only [F,dite_eq_left y.property]
  have hi : IntegrableOn F (Ioo x.val (1 : ℝ)) volume := by
    apply (integrableOn_iff_comap_subtypeVal (f := F) (μ := volume) measurableSet_Ioo).mpr
    apply f.property.congr
    filter_upwards [] with y
    exact (he y).symm
  calc
    _ = ∫ y in x.val..(1 : ℝ), F y := by
      rw [intervalIntegral.integral_of_le x.property.2.le,integral_Ioc_eq_integral_Ioo,
        ← integral_subtype_comap measurableSet_Ioo F]
      apply integral_congr_ae
      filter_upwards [] with y
      exact (he y).symm
    _ = (1-x.val) * ∫ t in (0 : ℝ)..1, F (1-(1-x.val)*t) := by
      simpa only [smul_eq_mul,mul_zero,sub_zero,mul_one,sub_sub_cancel]
        using (intervalIntegral.smul_integral_comp_sub_mul (E := ℝ) F
          (a := 0) (b := 1) (1-x.val) 1).symm
    _ = _ := by
      congr 1
      rw [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo,
        ← integral_subtype_comap measurableSet_Ioo (fun t ↦ F (1-(1-x.val)*t))]
      apply integral_congr_ae
      filter_upwards [] with t
      exact he ⟨1-(1-x.val)*t.val, by
        have hL : 0 < 1-x.val := by linarith [x.property.2]
        constructor
        · linarith [mul_lt_mul_of_pos_left t.property.2 hL]
        · linarith [mul_pos hL t.property.1]⟩
private theorem gegenbauer_affine_algebra (α lam : ℝ) (x : Ioo (-1 : ℝ) 1) (t : Ioo (0 : ℝ) 1) :
    (x.val+1) * ((x.val-((x.val+1)*t.val-1))^α * ((1 - (((x.val+1)*t.val-1) : ℝ) ^ 2) ^ ((lam) - 1 / 2))) =
      (2 : ℝ)^(lam-1/2)*(x.val+1)^(α+lam+1/2) *
        (t.val^(lam-1/2)*(1-t.val)^α/(1-((x.val+1)/2)*t.val)^(1/2-lam)) := by
  have hL : 0 < x.val+1 := by linarith [x.property.1]
  have hD : 0 < 1-((x.val+1)/2)*t.val := by
    have hz : (x.val+1)/2 < 1 := by linarith [x.property.2]
    have hz0 : 0 ≤ (x.val+1)/2 := by positivity
    have hh := (mul_le_of_le_one_right hz0 t.property.2.le).trans_lt hz
    linarith
  rw [show x.val-((x.val+1)*t.val-1) = (x.val+1)*(1-t.val) by ring,
    show 1-((x.val+1)*t.val-1)^2 = ((x.val+1)*t.val)*(2*(1-((x.val+1)/2)*t.val)) by ring,
    mul_rpow hL.le (by linarith [t.property.2] : 0 ≤ 1-t.val),
    mul_rpow (mul_nonneg hL.le t.property.1.le) (by positivity),
    mul_rpow hL.le t.property.1.le, mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD.le,
    show α+lam+1/2 = 1+α+(lam-1/2) by ring,
    rpow_add hL, rpow_add hL, rpow_one,
    show 1/2-lam = -(lam-1/2) by ring, rpow_neg hD.le, div_inv_eq_mul]
  ring

private theorem gegenbauer_right_affine_algebra (α lam : ℝ)
    (x : Ioo (-1 : ℝ) 1) (t : Ioo (0 : ℝ) 1) :
    (1-x.val) * ((1-(1-x.val)*t.val-x.val)^α *
      (1-(1-(1-x.val)*t.val)^2)^(lam-1/2)) =
      (2 : ℝ)^(lam-1/2)*(1-x.val)^(α+lam+1/2) *
        (t.val^(lam-1/2)*(1-t.val)^α/(1-((1-x.val)/2)*t.val)^(1/2-lam)) := by
  have h := gegenbauer_affine_algebra α lam
    ⟨-x.val,by constructor <;> linarith [x.property.1,x.property.2]⟩ t
  dsimp only at h
  rw [show -x.val+1 = 1-x.val by ring,
    show -x.val-((1-x.val)*t.val-1) = 1-(1-x.val)*t.val-x.val by ring,
    show (1-x.val)*t.val-1 = -(1-(1-x.val)*t.val) by ring,neg_sq] at h
  exact h

/-- Classical left Gauss formula, with the weighted input restricted to its side. -/
theorem powerLawLeft_gegenbauerWeight_hypergeometricOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    let c := GammaPoint.ofPos (α.val+lam.val+3/2)
      (by linarith [show -1 < α.val from α.property, show -(1/2) < lam.val from lam.property])
    let p := GaussParameters.ofNoPole (1/2-lam.val) (lam.val+1/2) c.val c.property
    let z : Metric.ball (0 : ℝ) 1 := ⟨(x.val+1)/2, by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [x.property.1,x.property.2]⟩
    powerLawLeft ((PowerLawInput.gegenbauerWeight α lam x).left ⟨x.val,Ioo_subset_Icc_self x.property⟩) =
      (2 : ℝ)^(lam.val-1/2)*(x.val+1)^(α.val+lam.val+1/2) *
        ((GammaOn (.ofPos (lam.val+1/2) (by linarith [show -(1/2) < lam.val from lam.property])) *
          GammaOn (.ofPos (α.val+1) (by linarith [show -1 < α.val from α.property])) / GammaOn c) *
          ordinaryHypergeometricOn p (.ofUnitDisk p z)) := by
  dsimp only
  let bp : Ioi (0 : ℝ) := ⟨lam.val+1/2, (by linarith [show -(1/2) < lam.val from lam.property] : (0 : ℝ) < lam.val+1/2)⟩
  let dp : Ioi (0 : ℝ) := ⟨α.val+1, (by linarith [show -1 < α.val from α.property] : (0 : ℝ) < α.val+1)⟩
  let z : Metric.ball (0 : ℝ) 1 := ⟨(x.val+1)/2, by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [x.property.1,x.property.2]⟩
  have hE := (integral_eulerHypergeometricOn (1/2-lam.val) bp dp z).2
  have hv : powerLawLeft ((PowerLawInput.gegenbauerWeight α lam x).left ⟨x.val,Ioo_subset_Icc_self x.property⟩) =
      (2 : ℝ)^(lam.val-1/2)*(x.val+1)^(α.val+lam.val+1/2) *
        ∫ t : Ioo (0 : ℝ) 1, t.val^(bp.val-1)*(1-t.val)^(dp.val-1)/
          (1-z.val*t.val)^(1/2-lam.val) ∂Measure.comap Subtype.val volume := by
    rw [left_affine_integral α.val x,← integral_const_mul,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    change (x.val+1) * ((x.val-((x.val+1)*t.val-1))^α.val *
      (((Polynomial.gegenbauerWeight lam.val _) : ℝ) * 1)) = _
    rw [mul_one,Polynomial.gegenbauerWeight_apply]
    simpa only [bp,dp,z,add_sub_cancel_right,
      show lam.val+1/2-1 = lam.val-1/2 by ring] using
      gegenbauer_affine_algebra α.val lam.val x t
  have hc : (lam.val+1/2)+(α.val+1) = α.val+lam.val+3/2 := by ring
  let cp := GammaPoint.ofPos (α.val+lam.val+3/2)
    (by linarith [show -1 < α.val from α.property,show -(1/2) < lam.val from lam.property])
  let pg := GaussParameters.ofNoPole (1/2-lam.val) (lam.val+1/2) cp.val cp.property
  have hp : eulerGaussParameters (1/2-lam.val) bp dp = pg := by
    simp only [eulerGaussParameters,GaussParameters.ofNoPole,bp,dp,pg,cp,GammaPoint.ofPos,hc]
  have hg := congrArg (fun p : GaussParameters ℝ ↦ ordinaryHypergeometricOn p (.ofUnitDisk p z)) hp
  rw [hv,hE,hg]
  simp only [bp,dp,z,pg,cp,GammaPoint.ofPos,hc]

/-- Classical right Gauss formula, with the weighted input restricted to its side. -/
theorem powerLawRight_gegenbauerWeight_hypergeometricOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    let c := GammaPoint.ofPos (α.val+lam.val+3/2)
      (by linarith [show -1 < α.val from α.property, show -(1/2) < lam.val from lam.property])
    let p := GaussParameters.ofNoPole (1/2-lam.val) (lam.val+1/2) c.val c.property
    let z : Metric.ball (0 : ℝ) 1 := ⟨(1-x.val)/2, by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [x.property.1,x.property.2]⟩
    powerLawRight ((PowerLawInput.gegenbauerWeight α lam x).right ⟨x.val,Ioo_subset_Icc_self x.property⟩) =
      (2 : ℝ)^(lam.val-1/2)*(1-x.val)^(α.val+lam.val+1/2) *
        ((GammaOn (.ofPos (lam.val+1/2) (by linarith [show -(1/2) < lam.val from lam.property])) *
          GammaOn (.ofPos (α.val+1) (by linarith [show -1 < α.val from α.property])) / GammaOn c) *
          ordinaryHypergeometricOn p (.ofUnitDisk p z)) := by
  dsimp only
  let bp : Ioi (0 : ℝ) := ⟨lam.val+1/2, (by linarith [show -(1/2) < lam.val from lam.property] : (0 : ℝ) < lam.val+1/2)⟩
  let dp : Ioi (0 : ℝ) := ⟨α.val+1, (by linarith [show -1 < α.val from α.property] : (0 : ℝ) < α.val+1)⟩
  let z : Metric.ball (0 : ℝ) 1 := ⟨(1-x.val)/2, by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [x.property.1,x.property.2]⟩
  have hE := (integral_eulerHypergeometricOn (1/2-lam.val) bp dp z).2
  have hv : powerLawRight ((PowerLawInput.gegenbauerWeight α lam x).right ⟨x.val,Ioo_subset_Icc_self x.property⟩) =
      (2 : ℝ)^(lam.val-1/2)*(1-x.val)^(α.val+lam.val+1/2) *
        ∫ t : Ioo (0 : ℝ) 1, t.val^(bp.val-1)*(1-t.val)^(dp.val-1)/
          (1-z.val*t.val)^(1/2-lam.val) ∂Measure.comap Subtype.val volume := by
    rw [right_affine_integral α.val x,← integral_const_mul,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    change (1-x.val) * ((1-(1-x.val)*t.val-x.val)^α.val *
      (((Polynomial.gegenbauerWeight lam.val _) : ℝ) * 1)) = _
    rw [mul_one,Polynomial.gegenbauerWeight_apply]
    simpa only [bp,dp,z,add_sub_cancel_right,
      show lam.val+1/2-1 = lam.val-1/2 by ring] using
      gegenbauer_right_affine_algebra α.val lam.val x t
  have hc : (lam.val+1/2)+(α.val+1) = α.val+lam.val+3/2 := by ring
  let cp := GammaPoint.ofPos (α.val+lam.val+3/2)
    (by linarith [show -1 < α.val from α.property,show -(1/2) < lam.val from lam.property])
  let pg := GaussParameters.ofNoPole (1/2-lam.val) (lam.val+1/2) cp.val cp.property
  have hp : eulerGaussParameters (1/2-lam.val) bp dp = pg := by
    simp only [eulerGaussParameters,GaussParameters.ofNoPole,bp,dp,pg,cp,GammaPoint.ofPos,hc]
  have hg := congrArg (fun p : GaussParameters ℝ ↦ ordinaryHypergeometricOn p (.ofUnitDisk p z)) hp
  rw [hv,hE,hg]
  simp only [bp,dp,z,pg,cp,GammaPoint.ofPos,hc]

/-- The split hypergeometric formula uses only classical values. -/
theorem powerLawIntegral_gegenbauerWeight_hypergeometricOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    let c := GammaPoint.ofPos (α.val+lam.val+3/2)
      (by linarith [show -1 < α.val from α.property, show -(1/2) < lam.val from lam.property])
    let p := GaussParameters.ofNoPole (1/2-lam.val) (lam.val+1/2) c.val c.property
    let zp : Metric.ball (0 : ℝ) 1 := ⟨(1+x.val)/2, by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [x.property.1,x.property.2]⟩
    let zm : Metric.ball (0 : ℝ) 1 := ⟨(1-x.val)/2, by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [x.property.1,x.property.2]⟩
    powerLawIntegral (.gegenbauerWeight α lam x) =
      (2 : ℝ)^(lam.val-1/2) *
        (GammaOn (.ofPos (lam.val+1/2) (by linarith [show -(1/2) < lam.val from lam.property])) *
          GammaOn (.ofPos (α.val+1) (by linarith [show -1 < α.val from α.property])) / GammaOn c) *
        ((1+x.val)^(α.val+lam.val+1/2)*ordinaryHypergeometricOn p (.ofUnitDisk p zp) +
          (1-x.val)^(α.val+lam.val+1/2)*ordinaryHypergeometricOn p (.ofUnitDisk p zm)) := by
  dsimp only
  rw [powerLawIntegral_eq_left_add_right ⟨x.val,Ioo_subset_Icc_self x.property⟩,
    powerLawLeft_gegenbauerWeight_hypergeometricOn,powerLawRight_gegenbauerWeight_hypergeometricOn]
  simp only [add_comm x.val 1]
  ring

private theorem gauss_parameters_congr {p q : GaussParameters ℝ}
    (ha : p.a = q.a) (hb : p.b = q.b) (hc : p.c = q.c) : p = q := by
  cases p
  cases q
  simp_all

private theorem gauss_zero (p : GaussParameters ℝ) :
    ordinaryHypergeometricOn p (.ofUnitDisk p ⟨0, by simp⟩) = 1 := by
  have hs := hasSum_ordinaryHypergeometricOn p ⟨0, by simp⟩
  have h : HasSum (fun n : ℕ ↦ ordinaryHypergeometricCoefficientOn p n * (0 : ℝ)^n) 1 := by
    convert (hasSum_ite_eq 0 (1 : ℝ)) using 1
    funext n
    by_cases hn : n = 0
    · subst n
      simp [ordinaryHypergeometricCoefficientOn]
    · simp [hn, zero_pow hn]
  exact hs.unique h

/-- The origin value contains only positive Gamma arguments. -/
theorem powerLawIntegral_gegenbauerWeight_originOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) :
    powerLawIntegral (.gegenbauerWeight α lam ⟨0, by constructor <;> norm_num⟩) =
      GammaOn (.ofPos ((α.val+1)/2) (by linarith [show -1 < α.val from α.property])) *
        GammaOn (.ofPos (lam.val+1/2) (by linarith [show -(1/2) < lam.val from lam.property])) /
        GammaOn (.ofPos (lam.val+α.val/2+1) (by linarith [show -1 < α.val from α.property,show -(1/2) < lam.val from lam.property])) := by
  let bp : Ioi (0 : ℝ) := ⟨(α.val+1)/2, (by linarith [show -1 < α.val from α.property] : (0 : ℝ) < (α.val+1)/2)⟩
  let dp : Ioi (0 : ℝ) := ⟨lam.val+1/2, (by linarith [show -(1/2) < lam.val from lam.property] : (0 : ℝ) < lam.val+1/2)⟩
  have hE := integral_eulerHypergeometricOn (0 : ℝ) bp dp ⟨0,by simp⟩
  simp only [zero_mul,sub_zero,rpow_zero,div_one,
    gauss_zero,mul_one] at hE
  let f : IntegrableInput (volume : Measure (Ioo (0 : ℝ) 1)) :=
    ⟨fun u ↦ u.val^(bp.val-1)*(1-u.val)^(dp.val-1),hE.1⟩
  have hs := integral_unitInterval_sq f
  let x0 : Ioo (-1 : ℝ) 1 := ⟨0,by constructor <;> norm_num⟩
  let u := PowerLawInput.gegenbauerWeight α lam x0
  have hchange : (∫ s : Ioo (0 : ℝ) 1, f.val s) =
      2*powerLawRight (u.right ⟨0,by constructor <;> norm_num⟩) := by
    rw [hs.2]
    change _ = 2*(∫ r : Ioo (0 : ℝ) 1, _ ∂Measure.comap Subtype.val volume)
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with r
    change 2*r.val*((r.val^2)^(bp.val-1)*(1-r.val^2)^(dp.val-1)) =
      2*((r.val-0)^α.val*(((Polynomial.gegenbauerWeight lam.val _) : ℝ)*1))
    rw [mul_one,sub_zero,Polynomial.gegenbauerWeight_apply]
    have he : (r.val^2)^(bp.val-1) = r.val^(α.val-1) := by
      rw [show r.val^2 = r.val^(2 : ℝ) by norm_cast,← rpow_mul r.property.1.le]
      congr 1
      dsimp only [bp]
      ring
    rw [he,show dp.val-1 = lam.val-1/2 by dsimp only [dp]; ring,
      show r.val^α.val = r.val^(α.val-1)*r.val by
        rw [← rpow_add_one r.property.1.ne',sub_add_cancel]]
    ring
  have hsplit := powerLawIntegral_eq_left_add_right ⟨0,by constructor <;> norm_num⟩ u
  have hlr : powerLawLeft (u.left ⟨0,by constructor <;> norm_num⟩) =
      powerLawRight (u.right ⟨0,by constructor <;> norm_num⟩) := by
    dsimp only [u]
    erw [powerLawLeft_gegenbauerWeight_hypergeometricOn α lam x0,powerLawRight_gegenbauerWeight_hypergeometricOn α lam x0]
    simp only [x0,zero_add,sub_zero]
  rw [hlr,← two_mul] at hsplit
  rw [hsplit,← hchange]
  change (∫ s : Ioo (0 : ℝ) 1, s.val^(bp.val-1)*(1-s.val)^(dp.val-1)
    ∂Measure.comap Subtype.val volume) = _
  rw [hE.2]
  simp only [bp,dp,show (α.val+1)/2+(lam.val+1/2) = lam.val+α.val/2+1 by ring]

/-- The symmetric power-law formula on its full interior domain. -/
theorem powerLawIntegral_gegenbauerWeight_hypergeometricSqOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    let p := GaussParameters.ofNoPole (-α.val/2) (-lam.val-α.val/2) (1/2 : ℝ)
      (GammaPoint.ofPos _ (by norm_num)).property
    let z : Metric.ball (0 : ℝ) 1 := ⟨x.val^2, by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [x.property.1,x.property.2]⟩
    powerLawIntegral (.gegenbauerWeight α lam x) =
      GammaOn (.ofPos ((α.val+1)/2) (by linarith [show -1 < α.val from α.property])) *
        GammaOn (.ofPos (lam.val+1/2) (by linarith [show -(1/2) < lam.val from lam.property])) /
        GammaOn (.ofPos (lam.val+α.val/2+1) (by linarith [show -1 < α.val from α.property,show -(1/2) < lam.val from lam.property])) *
        ordinaryHypergeometricOn p (.ofUnitDisk p z) := by
  dsimp only
  let t : Ioi (-1 : ℝ) := ⟨α.val+lam.val+1/2, by
    change -1 < α.val+lam.val+1/2
    linarith [show -1 < α.val from α.property,show -(1/2) < lam.val from lam.property]⟩
  let q₀ := GaussParameters.ofNoPole (1/2-lam.val) (1-(1/2-lam.val)) (t.val+1)
    (GammaPoint.ofPos _ (by linarith [show -1 < t.val from t.property])).property
  let r₀ := GaussParameters.ofNoPole ((1-t.val-(1/2-lam.val))/2)
    (((1/2-lam.val)-t.val)/2) (1/2 : ℝ) (GammaPoint.ofPos _ (by norm_num)).property
  let q := GaussParameters.ofNoPole (1/2-lam.val) (lam.val+1/2)
    (α.val+lam.val+3/2) (GammaPoint.ofPos _ (by
      linarith [show -1 < α.val from α.property,show -(1/2) < lam.val from lam.property])).property
  let r := GaussParameters.ofNoPole (-α.val/2) (-lam.val-α.val/2)
    (1/2 : ℝ) (GammaPoint.ofPos _ (by norm_num)).property
  have hq : q₀ = q := by
    apply gauss_parameters_congr <;> dsimp only [q₀,q,t,GaussParameters.ofNoPole] <;> ring
  have hr : r₀ = r := by
    apply gauss_parameters_congr <;> dsimp only [r₀,r,t,GaussParameters.ofNoPole] <;> ring
  have ht := ordinaryHypergeometricOn_even_quadratic (1/2-lam.val) t x
  change (1+x.val)^t.val * ordinaryHypergeometricOn q₀ (.ofUnitDisk q₀ _) +
    (1-x.val)^t.val * ordinaryHypergeometricOn q₀ (.ofUnitDisk q₀ _) =
    2 * ordinaryHypergeometricOn q₀ (.ofUnitDisk q₀ _) *
      ordinaryHypergeometricOn r₀ (.ofUnitDisk r₀ _) at ht
  rw [hq,hr] at ht
  dsimp only [t,q,r,GaussParameters.ofNoPole] at ht
  have h0 := powerLawIntegral_gegenbauerWeight_hypergeometricOn α lam ⟨0,by constructor <;> norm_num⟩
  rw [powerLawIntegral_gegenbauerWeight_originOn] at h0
  simp only [GaussParameters.ofNoPole,
    GammaOn,GammaPoint.ofPos,add_zero,sub_zero,one_rpow,one_mul] at h0
  have hs := powerLawIntegral_gegenbauerWeight_hypergeometricOn α lam x
  simp only [GaussParameters.ofNoPole,
    GammaOn,GammaPoint.ofPos] at hs ⊢
  rw [hs,ht,← mul_assoc]
  congr 1
  linear_combination -h0


end Real


namespace Real
/-- Continuity of the density on its actual open domain. -/
theorem continuous_gegenbauerWeightOn (lam : ℝ) :
    Continuous (fun y : Ioo (-1 : ℝ) 1 ↦ (Polynomial.gegenbauerWeight lam y : ℝ)) :=
  continuous_subtype_val.comp (Polynomial.gegenbauerWeight lam).continuous
/-- Every polynomial mode is a classical weighted input, including lambda zero. -/
def PowerLawInput.gegenbauerMode (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (n : ℕ) : PowerLawInput α.val x.val :=
  .gegenbauerContinuous α lam x
    ⟨fun y ↦ (gegenbauer lam.val n).eval y.val,
      (gegenbauer lam.val n).continuous.comp continuous_subtype_val⟩
theorem PowerLawInput.gegenbauerMode_apply (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (n : ℕ) (y : PowerLawDomain x.val) :
    (PowerLawInput.gegenbauerMode α lam x n).val y =
      (Polynomial.gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ) *
        (gegenbauer lam.val n).eval y.val := rfl
/-- Reflection of the endpoint input is still the same even density. -/
theorem PowerLawInput.gegenbauerEndpoint_reflect_apply (p : PowerLawEndpointParameters)
    (y : PowerLawDomain (-1)) :
    (PowerLawInput.gegenbauerEndpoint p).reflect.val y =
      (Polynomial.gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ) := by
  change (Polynomial.gegenbauerWeight p.val.2 ⟨-y.val, _⟩ : ℝ) = _
  simp only [Polynomial.gegenbauerWeight_apply, neg_sq]
/-- The reflected endpoint has the same positive-Gamma value. -/
theorem powerLawIntegral_gegenbauerEndpoint_neg (p : PowerLawEndpointParameters) :
    powerLawIntegral (PowerLawInput.gegenbauerEndpoint p).reflect =
      (2 : ℝ)^(p.val.1+2*p.val.2) *
        GammaOn (.ofPos (p.val.1+p.val.2+1/2) (by linarith [p.property.2])) *
        GammaOn (.ofPos (p.val.2+1/2) (by linarith [p.property.1])) /
        GammaOn (.ofPos (p.val.1+2*p.val.2+1) (by linarith [p.property.1,p.property.2])) := by
  rw [powerLawIntegral_neg, powerLawIntegral_gegenbauerEndpoint]
end Real
namespace Real
/-- Every classical weighted continuous input has an integrable product. -/
theorem integrable_powerLaw_gegenbauerContinuous (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    Integrable (fun y : PowerLawDomain x.val ↦ |x.val-y.val|^α.val *
      ((Polynomial.gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ) *
        f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩)) (Measure.comap Subtype.val volume) :=
  (PowerLawInput.gegenbauerContinuous α lam x f).property
/-- Left/right decomposition for every weighted continuous input. -/
theorem powerLawIntegral_gegenbauerContinuous_split (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    let u := PowerLawInput.gegenbauerContinuous α lam x f
    powerLawIntegral u = powerLawLeft (u.left ⟨x.val,Ioo_subset_Icc_self x.property⟩) +
      powerLawRight (u.right ⟨x.val,Ioo_subset_Icc_self x.property⟩) :=
  powerLawIntegral_eq_left_add_right ⟨x.val,Ioo_subset_Icc_self x.property⟩
    (PowerLawInput.gegenbauerContinuous α lam x f)
end Real

namespace Real



end Real
namespace Real
/-- The zeroth mode is the constant weighted input. -/
theorem PowerLawInput.gegenbauerMode_zero (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    PowerLawInput.gegenbauerMode α lam x 0 = PowerLawInput.gegenbauerWeight α lam x := by
  apply Subtype.ext
  funext y
  rw [PowerLawInput.gegenbauerMode_apply, PowerLawInput.gegenbauerWeight_apply,
    gegenbauer_zero, eval_one, mul_one]


/-- First mode for the classical left integral. -/
theorem powerLawLeft_gegenbauer_oneOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    let α' : Ioi (-1 : ℝ) := ⟨α.val+1, by change -1 < α.val+1; linarith [show -1 < α.val from α.property]⟩
    let xc : Icc (-1 : ℝ) 1 := ⟨x.val,Ioo_subset_Icc_self x.property⟩
    powerLawLeft ((PowerLawInput.gegenbauerMode α lam x 1).left xc) =
      2*lam.val*(x.val*powerLawLeft ((PowerLawInput.gegenbauerWeight α lam x).left xc) -
        powerLawLeft ((PowerLawInput.gegenbauerWeight α' lam x).left xc)) := by
  dsimp only
  let ap : Ioi (-1 : ℝ) := ⟨α.val+1,(by linarith [show -1 < α.val from α.property] : (-1 : ℝ) < α.val+1)⟩
  let xc : Icc (-1 : ℝ) 1 := ⟨x.val,Ioo_subset_Icc_self x.property⟩
  let f0 := (PowerLawInput.gegenbauerWeight α lam x).left xc
  let f1 := (PowerLawInput.gegenbauerWeight ap lam x).left xc
  have h0 := f0.property
  have h1 := f1.property
  calc
    _ = ∫ y : Ioo (-1 : ℝ) x.val, 2*lam.val*(x.val*((x.val-y.val)^α.val*f0.val y) -
        (x.val-y.val)^ap.val*f1.val y) ∂Measure.comap Subtype.val volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      change (x.val-y.val)^α.val*((Polynomial.gegenbauerWeight lam.val _ : ℝ)*
        (gegenbauer lam.val 1).eval y.val) =
        2*lam.val*(x.val*((x.val-y.val)^α.val*((Polynomial.gegenbauerWeight lam.val _ : ℝ)*1)) -
          (x.val-y.val)^(α.val+1)*((Polynomial.gegenbauerWeight lam.val _ : ℝ)*1))
      simp only [mul_one,gegenbauer_one,eval_mul,eval_C,eval_X]
      rw [rpow_add_one (sub_pos.mpr y.property.2).ne']
      ring
    _ = _ := by
      erw [integral_const_mul,integral_sub (h0.const_mul x.val) h1,integral_const_mul]
      rfl


/-- First mode for the classical right integral. -/
theorem powerLawRight_gegenbauer_oneOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    let α' : Ioi (-1 : ℝ) := ⟨α.val+1, by change -1 < α.val+1; linarith [show -1 < α.val from α.property]⟩
    let xc : Icc (-1 : ℝ) 1 := ⟨x.val,Ioo_subset_Icc_self x.property⟩
    powerLawRight ((PowerLawInput.gegenbauerMode α lam x 1).right xc) =
      2*lam.val*(x.val*powerLawRight ((PowerLawInput.gegenbauerWeight α lam x).right xc) +
        powerLawRight ((PowerLawInput.gegenbauerWeight α' lam x).right xc)) := by
  dsimp only
  let ap : Ioi (-1 : ℝ) := ⟨α.val+1,(by linarith [show -1 < α.val from α.property] : (-1 : ℝ) < α.val+1)⟩
  let xc : Icc (-1 : ℝ) 1 := ⟨x.val,Ioo_subset_Icc_self x.property⟩
  let f0 := (PowerLawInput.gegenbauerWeight α lam x).right xc
  let f1 := (PowerLawInput.gegenbauerWeight ap lam x).right xc
  have h0 := f0.property
  have h1 := f1.property
  calc
    _ = ∫ y : Ioo x.val (1 : ℝ), 2*lam.val*(x.val*((y.val-x.val)^α.val*f0.val y) +
        (y.val-x.val)^ap.val*f1.val y) ∂Measure.comap Subtype.val volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      change (y.val-x.val)^α.val*((Polynomial.gegenbauerWeight lam.val _ : ℝ)*
        (gegenbauer lam.val 1).eval y.val) =
        2*lam.val*(x.val*((y.val-x.val)^α.val*((Polynomial.gegenbauerWeight lam.val _ : ℝ)*1)) +
          (y.val-x.val)^(α.val+1)*((Polynomial.gegenbauerWeight lam.val _ : ℝ)*1))
      simp only [mul_one,gegenbauer_one,eval_mul,eval_C,eval_X]
      rw [rpow_add_one (sub_pos.mpr y.property.1).ne']
      ring
    _ = _ := by
      erw [integral_const_mul,integral_add (h0.const_mul x.val) h1,integral_const_mul]
      rfl


/-- First mode for the full classical integral. -/
theorem powerLawIntegral_gegenbauer_oneOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    let α' : Ioi (-1 : ℝ) := ⟨α.val+1, by change -1 < α.val+1; linarith [show -1 < α.val from α.property]⟩
    let xc : Icc (-1 : ℝ) 1 := ⟨x.val,Ioo_subset_Icc_self x.property⟩
    powerLawIntegral (PowerLawInput.gegenbauerMode α lam x 1) =
      2*lam.val*(x.val*powerLawIntegral (PowerLawInput.gegenbauerWeight α lam x) +
        powerLawRight ((PowerLawInput.gegenbauerWeight α' lam x).right xc) -
        powerLawLeft ((PowerLawInput.gegenbauerWeight α' lam x).left xc)) := by
  dsimp only
  rw [powerLawIntegral_eq_left_add_right ⟨x.val,Ioo_subset_Icc_self x.property⟩,
    powerLawLeft_gegenbauer_oneOn,powerLawRight_gegenbauer_oneOn,
    powerLawIntegral_eq_left_add_right ⟨x.val,Ioo_subset_Icc_self x.property⟩]
  ring

end Real
