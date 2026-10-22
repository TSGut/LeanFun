/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalWeighted
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Approximation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerOperator
/-! # Classical weighted power-law stability and approximation

All inputs carry weighted integrability, and spatial arguments lie in the open
interval. Uniform amplitude approximation gives uniform output approximation on
compact interior subsets. No polynomial compatibility condition is imposed.
Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/
public noncomputable section
open MeasureTheory Set Polynomial Filter
open scoped Topology NNReal
namespace Real

theorem abs_powerLawIntegral_le_weightedMass (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1)
    (u : PowerLawInput α.val x.val) (ε : ℝ≥0)
    (hu : ∀ y, |u.val y| ≤ (ε : ℝ) * (gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ)) :
    |powerLawIntegral u| ≤ (ε : ℝ) * powerLawIntegral (.gegenbauerWeight α lam x) := by
  have hi := (PowerLawInput.gegenbauerWeight α lam x).property.const_mul (ε : ℝ)
  unfold powerLawIntegral
  rw [← integral_const_mul]
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hi
  apply Filter.Eventually.of_forall
  intro y
  have hn : 0 ≤ |x.val-y.val|^α.val := rpow_nonneg (abs_nonneg _) _
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn,
    PowerLawInput.gegenbauerWeight_apply, mul_left_comm] using
    mul_le_mul_of_nonneg_left (hu y) hn

theorem abs_powerLawIntegral_sub_le_weightedMass (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1)
    (u v : PowerLawInput α.val x.val) (ε : ℝ≥0)
    (huv : ∀ y, |u.val y-v.val y| ≤ (ε : ℝ) *
      (gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ)) :
    |powerLawIntegral u-powerLawIntegral v| ≤
      (ε : ℝ) * powerLawIntegral (.gegenbauerWeight α lam x) := by
  let w : PowerLawInput α.val x.val := ⟨fun y ↦ u.val y-v.val y, by
    have hi := u.property.sub v.property
    change Integrable (fun y ↦ |x.val-y.val|^α.val*u.val y -
      |x.val-y.val|^α.val*v.val y) _ at hi
    simpa only [mul_sub] using hi⟩
  have he : powerLawIntegral u-powerLawIntegral v = powerLawIntegral w := by
    dsimp only [powerLawIntegral, w]
    rw [← integral_sub u.property v.property]
    simp only [mul_sub]
  rw [he]
  exact abs_powerLawIntegral_le_weightedMass α lam x w ε huv

theorem continuous_powerLawIntegral_weightedMass (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) :
    Continuous (fun x : Ioo (-1 : ℝ) 1 ↦
      powerLawIntegral (.gegenbauerWeight α lam x)) := by
  let p := GaussParameters.ofNoPole (-α.val/2) (-lam.val-α.val/2) (1/2 : ℝ)
    (GammaPoint.ofPos _ (by norm_num)).property
  have hc : Continuous (fun z : Metric.ball (0 : ℝ) 1 ↦
      ordinaryHypergeometricOn p (.ofUnitDisk p z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    obtain ⟨g,hg,ha⟩ := analyticOnOpen_ordinaryHypergeometricOn (isOpen_ball := Metric.isOpen_ball) p z
    have he : (fun y : Metric.ball (0 : ℝ) 1 ↦ g y.val) =
        (fun y ↦ ordinaryHypergeometricOn p (.ofUnitDisk p y)) := funext hg
    rw [← he]
    exact ha.continuousAt.comp (continuous_subtype_val : Continuous (Subtype.val : Metric.ball (0 : ℝ) 1 → ℝ)).continuousAt
  let z : Ioo (-1 : ℝ) 1 → Metric.ball (0 : ℝ) 1 := fun x ↦ ⟨x.val^2, by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [x.property.1,x.property.2]⟩
  have hz : Continuous z := by continuity
  have h := (hc.comp hz).const_mul
    (GammaOn (.ofPos ((α.val+1)/2) (by linarith [show -1 < α.val from α.property])) *
      GammaOn (.ofPos (lam.val+1/2) (by linarith [show -(1/2) < lam.val from lam.property])) /
      GammaOn (.ofPos (lam.val+α.val/2+1) (by linarith [show -1 < α.val from α.property,show -(1/2) < lam.val from lam.property])))
  apply h.congr
  intro x
  exact (powerLawIntegral_gegenbauerWeight_hypergeometricSqOn α lam x).symm

theorem exists_powerLawIntegral_weightedMass_bound (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) {K : Set (Ioo (-1 : ℝ) 1)} (hK : IsCompact K) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ K,
      powerLawIntegral (.gegenbauerWeight α lam x) ≤ M := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn
    (continuous_powerLawIntegral_weightedMass α lam).continuousOn
  refine ⟨|M|+1, by positivity, fun x hx ↦ ?_⟩
  exact (le_abs_self _).trans ((hM x hx).trans (by linarith [le_abs_self M]))
end Real
namespace Real

theorem abs_powerLawIntegral_gegenbauerContinuous_sub_le (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1)
    (f g : C(Icc (-1 : ℝ) 1, ℝ)) (ε : ℝ≥0)
    (hfg : ∀ y, |f y-g y| ≤ (ε : ℝ)) :
    |powerLawIntegral (.gegenbauerContinuous α lam x f)-
      powerLawIntegral (.gegenbauerContinuous α lam x g)| ≤
      (ε : ℝ)*powerLawIntegral (.gegenbauerWeight α lam x) := by
  apply abs_powerLawIntegral_sub_le_weightedMass
  intro y
  erw [PowerLawInput.gegenbauerContinuous_apply, PowerLawInput.gegenbauerContinuous_apply,
    ← mul_sub, abs_mul, abs_of_nonneg (gegenbauerWeight lam.val ⟨y.val,y.property.1⟩).property]
  exact (mul_le_mul_of_nonneg_left (hfg _) (gegenbauerWeight lam.val
    ⟨y.val,y.property.1⟩).property).trans_eq (mul_comm _ _)
end Real
namespace Real

end Real
namespace Real

theorem tendstoUniformlyOn_powerLaw_gegenbauerContinuous (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (f : C(Icc (-1 : ℝ) 1, ℝ))
    (u : ℕ → C(Icc (-1 : ℝ) 1, ℝ))
    (hconv : TendstoUniformly (fun n y ↦ u n y) f atTop)
    {K : Set (Ioo (-1 : ℝ) 1)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n x ↦ powerLawIntegral (.gegenbauerContinuous α lam x (u n)))
      (fun x ↦ powerLawIntegral (.gegenbauerContinuous α lam x f)) atTop K := by
  obtain ⟨M,hM,hb⟩ := exists_powerLawIntegral_weightedMass_bound α lam hK
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hconv (ε/(2*M)) (by positivity)] with n hn x hx
  have he := abs_powerLawIntegral_gegenbauerContinuous_sub_le α lam x f (u n)
    ⟨ε/(2*M), by positivity⟩ (fun y ↦ (show |f y-u n y| < ε/(2*M) from by
      simpa only [Real.dist_eq] using hn y).le)
  rw [Real.dist_eq]
  calc
    _ ≤ (ε/(2*M))*powerLawIntegral (.gegenbauerWeight α lam x) := he
    _ ≤ (ε/(2*M))*M := mul_le_mul_of_nonneg_left (hb x hx) (by positivity)
    _ < ε := by field_simp; nlinarith
end Real
namespace Real

theorem exists_polynomial_powerLaw_gegenbauerContinuous_approximation
    (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (f : C(Icc (-1 : ℝ) 1, ℝ)) {K : Set (Ioo (-1 : ℝ) 1)}
    (hK : IsCompact K) (ε : Ioi (0 : ℝ)) :
    ∃ p : ℝ[X], ∀ x ∈ K,
      |powerLawIntegral (.gegenbauerPolynomial α lam x p)-
        powerLawIntegral (.gegenbauerContinuous α lam x f)| < ε.val := by
  have hε : 0 < ε.val := ε.property
  obtain ⟨M,hM,hb⟩ := exists_powerLawIntegral_weightedMass_bound α lam hK
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f)
    (f.continuous.Icc_extend').continuousOn (ε.val/(2*M)) (by positivity)
  refine ⟨p, fun x hx ↦ ?_⟩
  have hfg (y : Icc (-1 : ℝ) 1) : |p.eval y.val-f y| ≤ ε.val/(2*M) := by
    have h := (hp y.val y.property).le
    simpa only [IccExtend, Function.comp_apply, projIcc_of_mem _ y.property] using h
  have he := abs_powerLawIntegral_gegenbauerContinuous_sub_le α lam x
    ⟨fun y ↦ p.eval y.val,p.continuous.comp continuous_subtype_val⟩ f
    ⟨ε.val/(2*M), by positivity⟩ hfg
  calc
    _ ≤ (ε.val/(2*M))*powerLawIntegral (.gegenbauerWeight α lam x) := he
    _ ≤ (ε.val/(2*M))*M := mul_le_mul_of_nonneg_left (hb x hx) (by positivity)
    _ < ε.val := by field_simp; nlinarith
end Real
namespace Real

theorem abs_powerLawIntegral_gegenbauerContinuous_pair_sub_le
    (α β : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (f g : C(Icc (-1 : ℝ) 1, ℝ)) (ε : ℝ≥0)
    (a b : ℝ) (hfg : ∀ y, |f y-g y| ≤ (ε : ℝ)) :
    |(a*powerLawIntegral (.gegenbauerContinuous α lam x f)+
      b*powerLawIntegral (.gegenbauerContinuous β lam x f))-
      (a*powerLawIntegral (.gegenbauerContinuous α lam x g)+
      b*powerLawIntegral (.gegenbauerContinuous β lam x g))| ≤
      (ε : ℝ)*(|a| *powerLawIntegral (.gegenbauerWeight α lam x)+
        |b| *powerLawIntegral (.gegenbauerWeight β lam x)) := by
  have ha := abs_powerLawIntegral_gegenbauerContinuous_sub_le α lam x f g ε hfg
  have hb := abs_powerLawIntegral_gegenbauerContinuous_sub_le β lam x f g ε hfg
  calc
    _ = |a*(powerLawIntegral (.gegenbauerContinuous α lam x f)-
          powerLawIntegral (.gegenbauerContinuous α lam x g))+
        b*(powerLawIntegral (.gegenbauerContinuous β lam x f)-
          powerLawIntegral (.gegenbauerContinuous β lam x g))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ |a| *((ε : ℝ)*powerLawIntegral (.gegenbauerWeight α lam x))+
        |b| *((ε : ℝ)*powerLawIntegral (.gegenbauerWeight β lam x)) := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
    _ = _ := by ring
end Real
