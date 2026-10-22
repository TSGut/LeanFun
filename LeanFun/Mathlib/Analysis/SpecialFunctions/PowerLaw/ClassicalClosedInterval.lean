/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalWeighted
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClosedInterval
/-! # Classical power-law inputs on the closed output interval

The combined endpoint exponent is part of the parameter domain. The integration
variable excludes endpoint and diagonal singularities; integrability is bundled.
Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/
open MeasureTheory Set Polynomial Filter
open scoped Topology NNReal
@[expose] public noncomputable section
namespace Real
abbrev PowerLawClosedParameters := {p : ℝ × ℝ // -1 < p.1 ∧ -(1/2) < p.2 ∧ -(1/2) < p.1+p.2}

def PowerLawInput.gegenbauerWeightClosed (p : PowerLawClosedParameters)
    (x : Icc (-1 : ℝ) 1) : PowerLawInput p.val.1 x.val := by
  refine ⟨fun y ↦ (Polynomial.gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ), ?_⟩
  rcases x with ⟨x,hx⟩
  rcases eq_or_lt_of_le hx.1 with he | hl
  · subst x
    have hi := (PowerLawInput.gegenbauerEndpoint ⟨p.val,p.property.2⟩).reflect.property
    simpa only [PowerLawInput.gegenbauerEndpoint_reflect_apply] using hi
  rcases lt_or_eq_of_le hx.2 with hr | he
  · have hi := (PowerLawInput.gegenbauerWeight ⟨p.val.1,p.property.1⟩
      ⟨p.val.2,p.property.2.1⟩ ⟨x,hl,hr⟩).property
    simpa only [PowerLawInput.gegenbauerWeight_apply] using hi
  · subst x
    exact (PowerLawInput.gegenbauerEndpoint ⟨p.val,p.property.2⟩).property
def PowerLawInput.gegenbauerContinuousClosed (p : PowerLawClosedParameters)
    (x : Icc (-1 : ℝ) 1) (f : C(Icc (-1 : ℝ) 1, ℝ)) : PowerLawInput p.val.1 x.val := by
  refine ⟨fun y ↦ (Polynomial.gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ)*
    f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩, ?_⟩
  have hi := (PowerLawInput.gegenbauerWeightClosed p x).property
  have hc : Continuous (fun y : PowerLawDomain x.val ↦
      f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩) := by fun_prop
  have hb : ∀ᵐ y : PowerLawDomain x.val ∂Measure.comap Subtype.val volume,
      ‖f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩‖ ≤ ‖f‖ :=
    Eventually.of_forall (fun y ↦ ContinuousMap.norm_coe_le_norm f _)
  convert hi.mul_bdd hc.aestronglyMeasurable hb using 1
  funext y
  change |x.val-y.val|^p.val.1 * ((Polynomial.gegenbauerWeight p.val.2 _ : ℝ)*_) =
    (|x.val-y.val|^p.val.1 * (Polynomial.gegenbauerWeight p.val.2 _ : ℝ))*_
  ring

theorem PowerLawInput.gegenbauerContinuousClosed_apply (p : PowerLawClosedParameters)
    (x : Icc (-1 : ℝ) 1) (f : C(Icc (-1 : ℝ) 1, ℝ)) (y : PowerLawDomain x.val) :
    (PowerLawInput.gegenbauerContinuousClosed p x f).val y =
      (Polynomial.gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ)*
        f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩ := rfl

theorem PowerLawInput.gegenbauerWeightClosed_apply (p : PowerLawClosedParameters)
    (x : Icc (-1 : ℝ) 1) (y : PowerLawDomain x.val) :
    (PowerLawInput.gegenbauerWeightClosed p x).val y =
      (Polynomial.gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ) := rfl
end Real

namespace Real
theorem abs_powerLawIntegral_le_weightedMassClosed (p : PowerLawClosedParameters)
    (x : Icc (-1 : ℝ) 1)
    (u : PowerLawInput p.val.1 x.val) (ε : ℝ≥0)
    (hu : ∀ y, |u.val y| ≤ (ε : ℝ) * (Polynomial.gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ)) :
    |powerLawIntegral u| ≤ (ε : ℝ) * powerLawIntegral (.gegenbauerWeightClosed p x) := by
  have hi := (PowerLawInput.gegenbauerWeightClosed p x).property.const_mul (ε : ℝ)
  unfold powerLawIntegral
  rw [← integral_const_mul]
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hi
  apply Filter.Eventually.of_forall
  intro y
  have hn : 0 ≤ |x.val-y.val|^p.val.1 := rpow_nonneg (abs_nonneg _) _
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn,
    PowerLawInput.gegenbauerWeightClosed_apply, mul_left_comm] using
    mul_le_mul_of_nonneg_left (hu y) hn

theorem abs_powerLawIntegral_sub_le_weightedMassClosed (p : PowerLawClosedParameters)
    (x : Icc (-1 : ℝ) 1)
    (u v : PowerLawInput p.val.1 x.val) (ε : ℝ≥0)
    (huv : ∀ y, |u.val y-v.val y| ≤ (ε : ℝ) *
      (Polynomial.gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ)) :
    |powerLawIntegral u-powerLawIntegral v| ≤
      (ε : ℝ) * powerLawIntegral (.gegenbauerWeightClosed p x) := by
  let w : PowerLawInput p.val.1 x.val := ⟨fun y ↦ u.val y-v.val y, by
    have hi := u.property.sub v.property
    change Integrable (fun y ↦ |x.val-y.val|^p.val.1*u.val y -
      |x.val-y.val|^p.val.1*v.val y) _ at hi
    simpa only [mul_sub] using hi⟩
  have he : powerLawIntegral u-powerLawIntegral v = powerLawIntegral w := by
    dsimp only [powerLawIntegral, w]
    rw [← integral_sub u.property v.property]
    simp only [mul_sub]
  rw [he]
  exact abs_powerLawIntegral_le_weightedMassClosed p x w ε huv


end Real

namespace Real
theorem abs_powerLawIntegral_gegenbauerContinuousClosed_sub_le (p : PowerLawClosedParameters)
    (x : Icc (-1 : ℝ) 1)
    (f g : C(Icc (-1 : ℝ) 1, ℝ)) (ε : ℝ≥0)
    (hfg : ∀ y, |f y-g y| ≤ (ε : ℝ)) :
    |powerLawIntegral (.gegenbauerContinuousClosed p x f)-
      powerLawIntegral (.gegenbauerContinuousClosed p x g)| ≤
      (ε : ℝ)*powerLawIntegral (.gegenbauerWeightClosed p x) := by
  apply abs_powerLawIntegral_sub_le_weightedMassClosed
  intro y
  erw [PowerLawInput.gegenbauerContinuousClosed_apply, PowerLawInput.gegenbauerContinuousClosed_apply,
    ← mul_sub, abs_mul, abs_of_nonneg (Polynomial.gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩).property]
  exact (mul_le_mul_of_nonneg_left (hfg _) (Polynomial.gegenbauerWeight p.val.2
    ⟨y.val,y.property.1⟩).property).trans_eq (mul_comm _ _)
end Real
namespace Real


theorem powerLawIntegral_weightedMassClosed_le_unweighted
    (p : PowerLawClosedParameters) (hlam : 1/2 ≤ p.val.2)
    (x : Icc (-1 : ℝ) 1) :
    powerLawIntegral (.gegenbauerWeightClosed p x) ≤
      powerLawIntegral (.one ⟨p.val.1,p.property.1⟩ x) := by
  apply integral_mono (PowerLawInput.gegenbauerWeightClosed p x).property
    (PowerLawInput.one ⟨p.val.1,p.property.1⟩ x).property
  intro y
  change |x.val-y.val|^p.val.1 * (gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ) ≤
    |x.val-y.val|^p.val.1 * 1
  apply mul_le_mul_of_nonneg_left _ (rpow_nonneg (abs_nonneg _) _)
  rw [gegenbauerWeight_apply]
  simpa only [one_rpow] using rpow_le_rpow
    (by nlinarith [y.property.1.1,y.property.1.2] : 0 ≤ 1-y.val^2)
    (by nlinarith : 1-y.val^2 ≤ 1) (by linarith : 0 ≤ p.val.2-1/2)

theorem powerLawIntegral_weightedMassClosed_le_of_half_le
    (p : PowerLawClosedParameters) (hlam : 1/2 ≤ p.val.2)
    (x : Icc (-1 : ℝ) 1) :
    powerLawIntegral (.gegenbauerWeightClosed p x) ≤
      (2*2^(p.val.1+1))/(p.val.1+1) := by
  apply (powerLawIntegral_weightedMassClosed_le_unweighted p hlam x).trans
  rw [powerLawIntegral_one]
  have hs : -1 < p.val.1 := p.property.1
  apply div_le_div_of_nonneg_right _ (by linarith)
  have h1 := rpow_le_rpow (by linarith [x.property.1] : 0 ≤ x.val+1)
    (by linarith [x.property.2] : x.val+1 ≤ 2) (by linarith : 0 ≤ p.val.1+1)
  have h2 := rpow_le_rpow (by linarith [x.property.2] : 0 ≤ 1-x.val)
    (by linarith [x.property.1] : 1-x.val ≤ 2) (by linarith : 0 ≤ p.val.1+1)
  linarith

theorem powerLawIntegral_weightedMassClosed_le_of_nonneg
    (p : PowerLawClosedParameters) (hα : 0 ≤ p.val.1)
    (x : Icc (-1 : ℝ) 1) :
    powerLawIntegral (.gegenbauerWeightClosed p x) ≤
      (2 : ℝ)^p.val.1*powerLawIntegral (.gegenbauerWeight
        ⟨0,by norm_num⟩ ⟨p.val.2,p.property.2.1⟩ ⟨0,by constructor <;> norm_num⟩) := by
  let W : Ioo (-1 : ℝ) 1 → ℝ := fun y ↦ (Polynomial.gegenbauerWeight p.val.2 y : ℝ)
  have hlam : -(1/2 : ℝ) < p.val.2 := p.property.2.1
  have hW : Integrable W (Measure.comap Subtype.val volume) := by
    have h := Polynomial.integrable_jacobiWeight (α := p.val.2-1/2) (β := p.val.2-1/2)
      (by linarith) (by linarith)
    convert h using 1
    all_goals rfl
  have hx := integrable_integral_powerLawDomain x.val ⟨W,hW⟩
  have hz := integrable_integral_powerLawDomain 0 ⟨W,hW⟩
  have hb : powerLawIntegral (.gegenbauerWeightClosed p x) ≤
      (2 : ℝ)^p.val.1 * (∫ y : PowerLawDomain x.val,
        W ⟨y.val,y.property.1⟩ ∂Measure.comap Subtype.val volume) := by
    rw [← integral_const_mul]
    apply integral_mono (PowerLawInput.gegenbauerWeightClosed p x).property
      (hx.1.const_mul _)
    intro y
    change |x.val-y.val|^p.val.1 * W ⟨y.val,y.property.1⟩ ≤
      (2 : ℝ)^p.val.1 * W ⟨y.val,y.property.1⟩
    apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
    exact rpow_le_rpow (abs_nonneg _)
      (abs_le.mpr ⟨by linarith [x.property.1,y.property.1.2],
        by linarith [x.property.2,y.property.1.1]⟩) hα
  rw [hx.2,← hz.2] at hb
  convert hb using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [PowerLawInput.gegenbauerWeight_apply,rpow_zero,one_mul]
  rfl

theorem exists_powerLawIntegral_weightedMassClosed_bound
    (p : PowerLawClosedParameters) (hregime : 0 ≤ p.val.1 ∨ 1/2 ≤ p.val.2) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : Icc (-1 : ℝ) 1,
      powerLawIntegral (.gegenbauerWeightClosed p x) ≤ M := by
  rcases hregime with hα | hlam
  · let B := (2 : ℝ)^p.val.1 * powerLawIntegral (.gegenbauerWeight
        ⟨0,by norm_num⟩ ⟨p.val.2,p.property.2.1⟩ ⟨0,by constructor <;> norm_num⟩)
    refine ⟨|B|+1, by linarith [abs_nonneg B], fun x ↦ ?_⟩
    exact (powerLawIntegral_weightedMassClosed_le_of_nonneg p hα x).trans
      ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one))
  · refine ⟨(2*2^(p.val.1+1))/(p.val.1+1), ?_,
      fun x ↦ powerLawIntegral_weightedMassClosed_le_of_half_le p hlam x⟩
    have hα : -1 < p.val.1 := p.property.1
    exact div_pos (mul_pos (by norm_num) (rpow_pos_of_pos (by norm_num) _)) (by linarith)
end Real
namespace Real

theorem tendstoUniformly_powerLaw_gegenbauerContinuousClosed
    (p : PowerLawClosedParameters) (M : Ioi (0 : ℝ))
    (hb : ∀ x : Icc (-1 : ℝ) 1,
      powerLawIntegral (.gegenbauerWeightClosed p x) ≤ M.val)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) (u : ℕ → C(Icc (-1 : ℝ) 1, ℝ))
    (hconv : TendstoUniformly (fun n y ↦ u n y) f atTop) :
    TendstoUniformly
      (fun n x ↦ powerLawIntegral (.gegenbauerContinuousClosed p x (u n)))
      (fun x ↦ powerLawIntegral (.gegenbauerContinuousClosed p x f)) atTop := by
  have hM : 0 < M.val := M.property
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hconv (ε/(2*M.val)) (by positivity)] with n hn x
  have he := abs_powerLawIntegral_gegenbauerContinuousClosed_sub_le p x f (u n)
    ⟨ε/(2*M.val),by positivity⟩ (fun y ↦ (show |f y-u n y| < ε/(2*M.val) from by
      simpa only [Real.dist_eq] using hn y).le)
  rw [Real.dist_eq]
  calc
    _ ≤ (ε/(2*M.val))*powerLawIntegral (.gegenbauerWeightClosed p x) := he
    _ ≤ (ε/(2*M.val))*M.val := mul_le_mul_of_nonneg_left (hb x) (by positivity)
    _ < ε := by field_simp; nlinarith
end Real
namespace Real

theorem PowerLawInput.gegenbauerContinuousClosed_integrable
    (p : PowerLawClosedParameters) (x : Icc (-1 : ℝ) 1)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    Integrable (fun y : PowerLawDomain x.val ↦ |x.val-y.val|^p.val.1*
      (Polynomial.gegenbauerWeight p.val.2 ⟨y.val,y.property.1⟩ : ℝ)*
      f ⟨y.val,Ioo_subset_Icc_self y.property.1⟩) (Measure.comap Subtype.val volume) := by
  simpa only [PowerLawInput.gegenbauerContinuousClosed, mul_assoc] using
    (PowerLawInput.gegenbauerContinuousClosed p x f).property
end Real
