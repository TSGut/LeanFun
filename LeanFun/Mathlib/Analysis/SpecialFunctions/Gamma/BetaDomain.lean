/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Convolution

/-! # The classical Euler Beta integral
Both parameters are in the Euler half-plane and the integration variable lies
strictly between zero and one. Reference: DLMF5.12.1.
-/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Complex

/-- The Euler half-plane for a Beta parameter. -/
abbrev BetaParameter := {z : ℂ // 0 < z.re}

/-- The classical Euler Beta integral, without endpoint power assignments. -/
def betaIntegralOn (a b : BetaParameter) : ℂ :=
  ∫ t : Ioo (0 : ℝ) 1, (t.val : ℂ) ^ (a.val - 1) *
    (1 - (t.val : ℂ)) ^ (b.val - 1) ∂Measure.comap Subtype.val volume

private theorem exists_positive_power (s : BetaParameter) :
    ∃ P : ℝ → ℂ, (∀ x : ℝ, 0 < x → P x = (x : ℂ)^(s.val-1)) ∧
      (∀ c : ℝ, 0 < c → IntervalIntegrable P volume 0 c) ∧
      (∀ x : ℝ, 0 < x → ContinuousAt P x) := by
  let P : ℝ → ℂ := fun x ↦ if 0 < x then (x : ℂ)^(s.val-1) else 0
  have he (x : ℝ) (hx : 0 < x) : P x = (x : ℂ)^(s.val-1) := by simp only [P,ite_eq_left hx]
  refine ⟨P,he,?_,?_⟩
  · intro c hc
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (f := P) hc.le]
    have hi := (intervalIntegral.integrableOn_Ioo_cpow_iff (s := s.val-1) hc).mpr
      (by have hs : 0 < s.val.re := s.property; simp only [sub_re,one_re]; linarith)
    apply hi.congr_fun _ measurableSet_Ioo
    intro x hx
    exact (he x hx.1).symm
  · intro x hx
    have hr : ContinuousAt (fun t : ℝ ↦ (t : ℂ)^(s.val-1)) x :=
      (continuousAt_cpow_const (b := s.val-1) (Or.inl hx)).comp continuous_ofReal.continuousAt
    apply hr.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    exact he t ht
private theorem exists_beta_representative (a b : BetaParameter) :
    ∃ B : ℝ → ℂ,
      (∀ t : Ioo (0 : ℝ) 1, B t.val = (t.val : ℂ)^(a.val-1)*(1-(t.val : ℂ))^(b.val-1)) ∧
      IntervalIntegrable B volume 0 1 := by
  obtain ⟨P,hP,hiP,hcP⟩ := exists_positive_power a
  obtain ⟨Q,hQ,hiQ,hcQ⟩ := exists_positive_power b
  let B : ℝ → ℂ := fun t ↦ P t * Q (1-t)
  have hQ' : IntervalIntegrable (fun t ↦ Q (1-t)) volume 0 1 := by
    simpa only [sub_zero,sub_self] using ((hiQ 1 zero_lt_one).comp_sub_left 1).symm
  refine ⟨B,?_,?_⟩
  · intro t
    dsimp only [B]
    rw [hP t.val t.property.1,hQ (1-t.val) (by linarith [t.property.2]),ofReal_sub,ofReal_one]
  · have hl : IntervalIntegrable B volume 0 (1/2) := by
      apply ((hiP 1 zero_lt_one).mono_set (by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl (by norm_num))).mul_continuousOn
      apply continuousOn_of_forall_continuousAt
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at hx
      exact (hcQ (1-x) (by linarith [hx.2])).comp (continuousAt_const.sub continuousAt_id)
    have hr : IntervalIntegrable B volume (1/2) 1 := by
      apply (hQ'.mono_set (by
        rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc (by norm_num) le_rfl)).continuousOn_mul
      apply continuousOn_of_forall_continuousAt
      intro x hx
      rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at hx
      exact hcP x (by linarith [hx.1])
    exact hl.trans hr

/-- Every input in the typed domain gives an integrable Beta integrand. -/
theorem integrable_betaIntegralOn (a b : BetaParameter) :
    Integrable (fun t : Ioo (0 : ℝ) 1 ↦ (t.val : ℂ) ^ (a.val - 1) *
      (1 - (t.val : ℂ)) ^ (b.val - 1)) (Measure.comap Subtype.val volume) := by
  obtain ⟨B,hB,hi⟩ := exists_beta_representative a b
  have hI := (intervalIntegrable_iff_integrableOn_Ioo_of_le (f := B) (by norm_num : (0 : ℝ) ≤ 1)).mp hi
  have h := (integrableOn_iff_comap_subtypeVal (f := B) (μ := volume) measurableSet_Ioo).mp hI
  apply h.congr
  filter_upwards [] with t
  exact hB t

private theorem safe_beta_scaled (a b : BetaParameter)
    (P Q : ℝ → ℂ)
    (hP : ∀ y : ℝ, 0 < y → P y = (y : ℂ)^(a.val-1))
    (hQ : ∀ y : ℝ, 0 < y → Q y = (y : ℂ)^(b.val-1))
    (x : ℝ) (hx : 0 < x) :
    (∫ y in 0..x, P y * Q (x-y)) =
      (x : ℂ)^(a.val+b.val-1) * betaIntegralOn a b := by
  let B : ℝ → ℂ := fun y ↦ P y * Q (1-y)
  have hB : (∫ y in 0..1, B y) = betaIntegralOn a b := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rw [← integral_subtype_comap measurableSet_Ioo B]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [B]
    rw [hP y.val y.property.1, hQ (1-y.val) (by linarith [y.property.2]),
      ofReal_sub, ofReal_one]
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have A : (x : ℂ)^(a.val+b.val-1) =
      x * ((x : ℂ)^(a.val-1)*(x : ℂ)^(b.val-1)) := by
    rw [(by abel : a.val+b.val-1 = 1+(a.val-1)+(b.val-1)),
      cpow_add _ _ hx', cpow_add 1 _ hx', cpow_one, mul_assoc]
  rw [A, ← hB, mul_assoc, ← intervalIntegral.integral_const_mul, ← real_smul]
  have hchange := intervalIntegral.integral_comp_div
    (fun y ↦ (x : ℂ)^(a.val-1)*(x : ℂ)^(b.val-1)*B y)
    (a := 0) (b := x) hx.ne'
  simp only [zero_div, div_self hx.ne'] at hchange
  rw [← hchange]
  apply intervalIntegral.integral_congr_Ioo_of_le hx.le
  intro y hy
  dsimp only [B]
  rw [hP y hy.1, hQ (x-y) (by linarith [hy.2]),
    hP (y/x) (div_pos hy.1 hx), hQ (1-y/x) (sub_pos.mpr ((div_lt_one hx).mpr hy.2))]
  rw [mul_mul_mul_comm]
  congr 1
  · rw [← mul_cpow_ofReal_nonneg hx.le (div_pos hy.1 hx).le,
      ofReal_div, mul_div_cancel₀ _ hx']
  · rw [← mul_cpow_ofReal_nonneg hx.le (sub_pos.mpr ((div_lt_one hx).mpr hy.2)).le]
    congr 1
    push_cast
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hx']
private theorem safe_gamma_beta (a b : BetaParameter) :
    Gamma a.val * Gamma b.val = Gamma (a.val+b.val) * betaIntegralOn a b := by
  obtain ⟨P,hP,hiP,hcP⟩ := exists_positive_power a
  obtain ⟨Q,hQ,hiQ,hcQ⟩ := exists_positive_power b
  let F : ℝ → ℂ := fun y ↦ (Real.exp (-y) : ℂ) * P y
  let G : ℝ → ℂ := fun y ↦ (Real.exp (-y) : ℂ) * Q y
  have hf : IntegrableOn F (Ioi 0) volume := by
    apply (GammaIntegral_convergent a.property).congr_fun _ measurableSet_Ioi
    intro y hy
    dsimp only [F]
    rw [hP y hy]
  have hg : IntegrableOn G (Ioi 0) volume := by
    apply (GammaIntegral_convergent b.property).congr_fun _ measurableSet_Ioi
    intro y hy
    dsimp only [G]
    rw [hQ y hy]
  have vf : (∫ y in Ioi (0 : ℝ), F y) = Gamma a.val := by
    rw [Gamma_eq_integral a.property, GammaIntegral]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only [F]
    rw [hP y hy]
  have vg : (∫ y in Ioi (0 : ℝ), G y) = Gamma b.val := by
    rw [Gamma_eq_integral b.property, GammaIntegral]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only [G]
    rw [hQ y hy]
  have hc := integral_posConvolution hf hg (ContinuousLinearMap.mul ℝ ℂ)
  simp only [ContinuousLinearMap.mul_apply'] at hc
  rw [vf,vg] at hc
  rw [← hc, Gamma_eq_integral (show 0 < (a.val+b.val).re by
    rw [add_re]; exact add_pos a.property b.property), GammaIntegral,
    ← MeasureTheory.integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have he (y : ℝ) : (Real.exp (-y) : ℂ) * Real.exp (-(x-y)) = Real.exp (-x) := by
    rw [← ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  calc
    (∫ y in 0..x, F y * G (x-y)) =
        ∫ y in 0..x, (Real.exp (-x) : ℂ) * (P y * Q (x-y)) := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only [F,G]
      rw [mul_mul_mul_comm,he]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, safe_beta_scaled a b P Q hP hQ x hx]
      exact (mul_assoc _ _ _).symm

/-- The Beta--Gamma formula uses only Gamma values in the right half-plane. -/
theorem betaIntegralOn_eq_Gamma (a b : BetaParameter) :
    betaIntegralOn a b = GammaOn (.ofRePos a.val a.property) *
      GammaOn (.ofRePos b.val b.property) /
        GammaOn (.ofRePos (a.val + b.val) (by
          rw [add_re]; exact add_pos a.property b.property)) := by
  apply (eq_div_iff (GammaOn_ne_zero _)).mpr
  simpa only [GammaOn, GammaPoint.ofRePos, mul_comm] using (safe_gamma_beta a b).symm


/-- The Euler Beta value is nonzero throughout its classical domain. -/
theorem betaIntegralOn_ne_zero (a b : BetaParameter) : betaIntegralOn a b ≠ 0 := by
  rw [betaIntegralOn_eq_Gamma]
  exact div_ne_zero (mul_ne_zero (GammaOn_ne_zero _) (GammaOn_ne_zero _)) (GammaOn_ne_zero _)
end Complex
