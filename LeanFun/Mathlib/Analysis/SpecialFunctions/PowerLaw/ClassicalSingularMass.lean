/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalClosedInterval
/-! # Classical singular-kernel mass bounds

All negative powers use strictly positive bases. Integral inputs have their
weighted integrability bundled, including at the output endpoints.
Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/
public section
open MeasureTheory Polynomial Set Filter
open scoped Topology
namespace Real

theorem rpow_mul_rpow_le_add_rpowOn (a b : Ioi (0 : ℝ)) (p q : Iic (0 : ℝ)) :
    a.val^p.val*b.val^q.val ≤ a.val^(p.val+q.val)+b.val^(p.val+q.val) := by
  rcases le_total a.val b.val with hab | hba
  · calc
      _ ≤ a.val^p.val*a.val^q.val := mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_nonpos a.property hab q.property) (rpow_nonneg a.property.le _)
      _ = a.val^(p.val+q.val) := (rpow_add a.property p.val q.val).symm
      _ ≤ _ := le_add_of_nonneg_right (rpow_nonneg b.property.le _)
  · calc
      _ ≤ b.val^p.val*b.val^q.val := mul_le_mul_of_nonneg_right
        (rpow_le_rpow_of_nonpos b.property hba p.property) (rpow_nonneg b.property.le _)
      _ = b.val^(p.val+q.val) := (rpow_add b.property p.val q.val).symm
      _ ≤ _ := le_add_of_nonneg_left (rpow_nonneg a.property.le _)

theorem powerLaw_gegenbauerWeight_le_three_powersOn (α : Iio (0 : ℝ))
    (lam : Iic (1/2 : ℝ)) (x : ℝ) (y : PowerLawDomain x) :
    |x-y.val|^α.val*(Polynomial.gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ) ≤
      |x-y.val|^(α.val+(lam.val-1/2))+|1-y.val|^(α.val+(lam.val-1/2))+
        |(-1 : ℝ)-y.val|^(α.val+(lam.val-1/2)) := by
  have hα : α.val < 0 := α.property
  have hlam : lam.val ≤ 1/2 := lam.property
  have hy : y.val ∈ Ioo (-1 : ℝ) 1 := y.property.1
  have ha : 0 < |x-y.val| := powerLawDomain_base_pos y
  have hβ : lam.val-1/2 ≤ 0 := by linarith
  change |x-y.val|^α.val * (jacobiWeight (lam.val-1/2) (lam.val-1/2) ⟨y.val,hy⟩ : ℝ) ≤ _
  rw [jacobiWeight_apply]
  have hminus : 0 < 1-y.val := by linarith [hy.2]
  have hplus : 0 < 1+y.val := by linarith [hy.1]
  have he1 : |1-y.val| = 1-y.val := abs_of_pos hminus
  have he2 : |(-1 : ℝ)-y.val| = 1+y.val := by rw [abs_of_neg (by linarith [hy.1])]; ring
  rw [he1, he2]
  by_cases hy0 : 0 ≤ y.val
  · have hw : (1+y.val)^(lam.val-1/2) ≤ 1 := by
      simpa using rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        (by linarith : 1 ≤ 1+y.val) hβ
    calc
      _ ≤ |x-y.val|^α.val * (1-y.val)^(lam.val-1/2) := by
        nlinarith [mul_nonneg (rpow_nonneg (abs_nonneg (x-y.val)) α.val)
          (rpow_nonneg hminus.le (lam.val-1/2)), mul_le_mul_of_nonneg_left hw
          (mul_nonneg (rpow_nonneg (abs_nonneg (x-y.val)) α.val) (rpow_nonneg hminus.le (lam.val-1/2)))]
      _ ≤ |x-y.val|^(α.val+(lam.val-1/2))+(1-y.val)^(α.val+(lam.val-1/2)) :=
        rpow_mul_rpow_le_add_rpowOn ⟨|x-y.val|,ha⟩ ⟨1-y.val,hminus⟩
          ⟨α.val,hα.le⟩ ⟨lam.val-1/2,hβ⟩
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hw : (1-y.val)^(lam.val-1/2) ≤ 1 := by
      simpa using rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        (by linarith : 1 ≤ 1-y.val) hβ
    calc
      _ ≤ |x-y.val|^α.val * (1+y.val)^(lam.val-1/2) := by
        nlinarith [mul_le_mul_of_nonneg_left hw
          (mul_nonneg (rpow_nonneg (abs_nonneg (x-y.val)) α.val) (rpow_nonneg hplus.le (lam.val-1/2)))]
      _ ≤ |x-y.val|^(α.val+(lam.val-1/2))+(1+y.val)^(α.val+(lam.val-1/2)) :=
        rpow_mul_rpow_le_add_rpowOn ⟨|x-y.val|,ha⟩ ⟨1+y.val,hplus⟩
          ⟨α.val,hα.le⟩ ⟨lam.val-1/2,hβ⟩
      _ ≤ _ := by have := rpow_nonneg hminus.le (α.val+(lam.val-1/2)); linarith



theorem powerLawIntegral_one_leOn (s : Ioi (-1 : ℝ)) (x : Icc (-1 : ℝ) 1) :
    powerLawIntegral (.one s x) ≤ 2*2^(s.val+1)/(s.val+1) := by
  rw [powerLawIntegral_one]
  have hs : -1 < s.val := s.property
  apply div_le_div_of_nonneg_right _ (by linarith)
  have h1 := rpow_le_rpow (by linarith [x.property.1] : 0 ≤ x.val+1)
    (by linarith [x.property.2] : x.val+1 ≤ 2) (by linarith : 0 ≤ s.val+1)
  have h2 := rpow_le_rpow (by linarith [x.property.2] : 0 ≤ 1-x.val)
    (by linarith [x.property.1] : 1-x.val ≤ 2) (by linarith : 0 ≤ s.val+1)
  linarith

theorem powerLawIntegral_weightedMassClosed_le_singular
    (p : PowerLawClosedParameters) (hα : p.val.1 < 0) (hlam : p.val.2 ≤ 1/2)
    (x : Icc (-1 : ℝ) 1) :
    powerLawIntegral (.gegenbauerWeightClosed p x) ≤
      6*2^(p.val.1+p.val.2+1/2)/(p.val.1+p.val.2+1/2) := by
  have hsum : -(1/2 : ℝ) < p.val.1+p.val.2 := p.property.2.2
  let s : Ioi (-1 : ℝ) := ⟨p.val.1+(p.val.2-1/2),(by linarith : (-1 : ℝ) < p.val.1+(p.val.2-1/2))⟩
  let P : Ioo (-1 : ℝ) 1 → ℝ := fun y ↦ (1-y.val)^s.val
  let Q : Ioo (-1 : ℝ) 1 → ℝ := fun y ↦ (y.val+1)^s.val
  let C : ℝ := 2^(s.val+1)/(s.val+1)
  have hP : Integrable P (Measure.comap Subtype.val volume) :=
    (integrable_powerLawLeft_kernel_and_integral s ⟨1,by norm_num⟩).1
  have hQ : Integrable Q (Measure.comap Subtype.val volume) := by
    simpa only [sub_neg_eq_add] using
      (integrable_powerLawRight_kernel_and_integral s ⟨-1,by norm_num⟩).1
  have vP : (∫ y : Ioo (-1 : ℝ) 1, P y ∂Measure.comap Subtype.val volume) = C := by
    convert (integrable_powerLawLeft_kernel_and_integral s ⟨1,by norm_num⟩).2 using 1; norm_num [C]
  have vQ : (∫ y : Ioo (-1 : ℝ) 1, Q y ∂Measure.comap Subtype.val volume) = C := by
    simpa only [Q,C,sub_neg_eq_add,one_add_one_eq_two] using
      (integrable_powerLawRight_kernel_and_integral s ⟨-1,by norm_num⟩).2
  have hp := integrable_integral_powerLawDomain x.val ⟨P,hP⟩
  have hq := integrable_integral_powerLawDomain x.val ⟨Q,hQ⟩
  have hk := integrable_powerLaw_kernel s x
  have hb : powerLawIntegral (.gegenbauerWeightClosed p x) ≤
      ∫ y : PowerLawDomain x.val, |x.val-y.val|^s.val +
        P ⟨y.val,y.property.1⟩ + Q ⟨y.val,y.property.1⟩ ∂Measure.comap Subtype.val volume := by
    apply integral_mono (PowerLawInput.gegenbauerWeightClosed p x).property ((hk.add hp.1).add hq.1)
    intro y
    have h := powerLaw_gegenbauerWeight_le_three_powersOn ⟨p.val.1,hα⟩ ⟨p.val.2,hlam⟩ x.val y
    rw [abs_of_pos (by linarith [y.property.1.2] : 0 < 1-y.val),
      abs_of_neg (by linarith [y.property.1.1] : (-1 : ℝ)-y.val < 0),neg_sub,sub_neg_eq_add] at h
    exact h
  change Integrable (fun y : PowerLawDomain x.val ↦ P ⟨y.val,y.property.1⟩) _ ∧ _ at hp
  change Integrable (fun y : PowerLawDomain x.val ↦ Q ⟨y.val,y.property.1⟩) _ ∧ _ at hq
  erw [integral_add (hk.add hp.1) hq.1,integral_add hk hp.1,hp.2,hq.2,vP,vQ] at hb
  have hC : (∫ y : PowerLawDomain x.val, |x.val-y.val|^s.val ∂Measure.comap Subtype.val volume) ≤ 2*C := by
    simpa only [powerLawIntegral,PowerLawInput.one,mul_one,C,mul_div_assoc] using powerLawIntegral_one_leOn s x
  have hs : -1 < s.val := s.property
  have hpos : 0 ≤ C := (div_pos (rpow_pos_of_pos (by norm_num) _) (by linarith)).le
  calc
    _ ≤ 6*C := by linarith
    _ = _ := by
      dsimp only [C]
      rw [show s.val+1 = p.val.1+p.val.2+1/2 by dsimp only [s]; ring]
      ring

theorem exists_powerLawIntegral_weightedMassClosed_bound_of_endpoint
    (p : PowerLawClosedParameters) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : Icc (-1 : ℝ) 1,
      powerLawIntegral (.gegenbauerWeightClosed p x) ≤ M := by
  by_cases hα : 0 ≤ p.val.1
  · exact exists_powerLawIntegral_weightedMassClosed_bound p (Or.inl hα)
  by_cases hlam : 1/2 ≤ p.val.2
  · exact exists_powerLawIntegral_weightedMassClosed_bound p (Or.inr hlam)
  refine ⟨6*2^(p.val.1+p.val.2+1/2)/(p.val.1+p.val.2+1/2), ?_, fun x ↦
    powerLawIntegral_weightedMassClosed_le_singular p (lt_of_not_ge hα)
      (le_of_lt (lt_of_not_ge hlam)) x⟩
  have hsum : -(1/2 : ℝ) < p.val.1+p.val.2 := p.property.2.2
  exact div_pos (mul_pos (by norm_num) (rpow_pos_of_pos (by norm_num) _)) (by linarith)

theorem tendstoUniformly_powerLaw_gegenbauerContinuousClosed_of_endpoint
    (p : PowerLawClosedParameters) (f : C(Icc (-1 : ℝ) 1, ℝ))
    (u : ℕ → C(Icc (-1 : ℝ) 1, ℝ))
    (hconv : TendstoUniformly (fun n y ↦ u n y) f atTop) :
    TendstoUniformly
      (fun n x ↦ powerLawIntegral (.gegenbauerContinuousClosed p x (u n)))
      (fun x ↦ powerLawIntegral (.gegenbauerContinuousClosed p x f)) atTop := by
  obtain ⟨M,hM,hb⟩ := exists_powerLawIntegral_weightedMassClosed_bound_of_endpoint p
  exact tendstoUniformly_powerLaw_gegenbauerContinuousClosed p ⟨M,hM⟩ hb f u hconv
end Real
