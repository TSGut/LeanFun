/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Polynomial
public import LeanFun.Mathlib.MeasureTheory.Integral.OpenIntervalFTC
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.WeightedDerivative
public import Mathlib.Topology.Algebra.Polynomial

/-! # Integration by parts for Gegenbauer power-law integrals

The shifted kernel exponent and shifted weight both vanish at the appropriate
endpoints. Thus no extra smoothness or endpoint restriction is needed.
Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Lemma 2.2.
-/

public section
open Set MeasureTheory Polynomial
namespace Real



end Real

open scoped Topology NNReal
namespace Real
attribute [local instance] Measure.Subtype.measureSpace
/-- Integration by parts with a continuous closed-domain primitive and integrable interior derivative. -/
theorem powerLawLeftPolynomial_gegenbauer_integrationByParts (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (n : ℕ) :
    ((n : ℝ)*((n : ℝ)+2*lam.val))*powerLawLeftPolynomial
        ⟨α.val+1,by change -1 < α.val+1; linarith [show -1 < α.val from α.property]⟩
        lam x (gegenbauer lam.val n) =
      -(α.val+1)*powerLawLeftPolynomial α
        ⟨lam.val+1,by change -(1/2 : ℝ) < lam.val+1; linarith [show -(1/2 : ℝ) < lam.val from lam.property]⟩
        x (gegenbauer lam.val n).derivative := by
  have ha : -1 < α.val := α.property
  have hl : -(1/2 : ℝ) < lam.val := lam.property
  let α' : Ioi (-1 : ℝ) := ⟨α.val+1,by change -1 < α.val+1; linarith⟩
  let lam' : Ioi (-(1/2) : ℝ) := ⟨lam.val+1,by change -(1/2 : ℝ) < lam.val+1; linarith⟩
  let c : ℝ≥0 := ⟨lam.val+1/2,by linarith⟩
  let p := gegenbauer lam.val n
  let D := (n : ℝ)*((n : ℝ)+2*lam.val)
  let j (y : Icc (-1 : ℝ) x.val) : Icc (-1 : ℝ) 1 :=
    ⟨y.val,y.property.1,y.property.2.trans x.property.2.le⟩
  have hW (y : Ioo (-1 : ℝ) 1) :
      (jacobiWeightClosed c c ⟨y.val,Ioo_subset_Icc_self y.property⟩ : ℝ) =
        (gegenbauerWeight (lam.val+1) y : ℝ) := by
    rw [jacobiWeightClosed_restrict]
    change (jacobiWeight (lam.val+1/2) (lam.val+1/2) y : ℝ) =
      (jacobiWeight (lam.val+1-1/2) (lam.val+1-1/2) y : ℝ)
    rw [show lam.val+1-1/2 = lam.val+1/2 by ring]
  let F : C(Icc (-1 : ℝ) x.val, ℝ) :=
    ⟨fun y ↦ (x.val-y.val)^(α.val+1)*(jacobiWeightClosed c c (j y) : ℝ)*p.derivative.eval y.val, by
      apply Continuous.mul
      · apply Continuous.mul
        · exact (continuous_const.sub continuous_subtype_val).rpow_const (fun _ ↦ Or.inr (by linarith))
        · exact NNReal.continuous_coe.comp ((jacobiWeightClosed c c).continuous.comp (by fun_prop))
      · exact p.derivative.continuous.comp continuous_subtype_val⟩
  let I := fun y : Ioo (-1 : ℝ) x.val ↦ (x.val-y.val)^α.val *
    (PowerLawLeftInput.gegenbauerPolynomial α lam' x p.derivative).val y
  let J := fun y : Ioo (-1 : ℝ) x.val ↦ (x.val-y.val)^α'.val *
    (PowerLawLeftInput.gegenbauerPolynomial α' lam x p).val y
  have hI : Integrable I volume := (PowerLawLeftInput.gegenbauerPolynomial α lam' x p.derivative).property
  have hJ : Integrable J volume := (PowerLawLeftInput.gegenbauerPolynomial α' lam x p).property
  let g : IntegrableInput (volume : Measure (Ioo (-1 : ℝ) x.val)) :=
    ⟨fun y ↦ -(α.val+1)*I y-D*J y,(hI.const_mul _).sub (hJ.const_mul _)⟩
  have hd (y : Ioo (-1 : ℝ) x.val) : HasDerivAtOnOpen
      ⟨Ioo (-1 : ℝ) x.val,isOpen_Ioo⟩
      (fun z ↦ F ⟨z.val,Ioo_subset_Icc_self z.property⟩) (g.val y) y := by
    let y' : Ioo (-1 : ℝ) 1 := ⟨y.val,y.property.1,y.property.2.trans x.property.2⟩
    obtain ⟨G,hG,hder⟩ := hasDerivAt_gegenbauerWeight_mul_derivative lam.val n y'
    have hb : 0 < x.val-y.val := sub_pos.mpr y.property.2
    have hk := ((hasDerivAt_abs_pos hb).comp y.val
      ((hasDerivAt_const y.val x.val).sub (hasDerivAt_id y.val))).rpow_const
      (p := α.val+1) (Or.inl (by change |x.val-y.val| ≠ 0; exact abs_ne_zero.mpr hb.ne'))
    refine ⟨fun t ↦ |x.val-t|^(α.val+1)*G t, ?_, ?_⟩
    · intro z
      change |x.val-z.val|^(α.val+1)*G z.val = _
      erw [abs_of_pos (sub_pos.mpr z.property.2),hG ⟨z.val,z.property.1,z.property.2.trans x.property.2⟩]
      change _ = (x.val-z.val)^(α.val+1)*(jacobiWeightClosed c c _ : ℝ)*p.derivative.eval z.val
      rw [hW ⟨z.val,z.property.1,z.property.2.trans x.property.2⟩]
      dsimp only [p]
      ring
    · apply (hk.mul hder).congr_deriv
      rw [hG y']
      dsimp only [g,I,J,α',lam',D,p,y']
      rw [PowerLawLeftInput.gegenbauerPolynomial_apply,PowerLawLeftInput.gegenbauerPolynomial_apply]
      dsimp only [Function.comp_apply]
      erw [abs_of_pos hb,show α.val+1-1 = α.val by ring]
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAtOnOpen x.property.1 F g hd
  have hright : F ⟨x.val,x.property.1.le,le_rfl⟩ = 0 := by
    dsimp only [F,ContinuousMap.coe_mk]
    rw [sub_self,zero_rpow (by linarith : α.val+1 ≠ 0),zero_mul,zero_mul]
  have hleft : F ⟨-1,le_rfl,x.property.1.le⟩ = 0 := by
    dsimp only [F,ContinuousMap.coe_mk]
    rw [jacobiWeightClosed_apply]
    change (x.val-(-1))^(α.val+1)*((1-(-1))^(lam.val+1/2)*(1+(-1))^(lam.val+1/2))*_ = 0
    norm_num [zero_rpow (by linarith : lam.val+1/2 ≠ 0)]
  rw [hright,hleft,sub_self] at hi
  change (∫ y, -(α.val+1)*I y-D*J y) = 0 at hi
  rw [integral_sub (hI.const_mul _) (hJ.const_mul _),integral_const_mul,integral_const_mul] at hi
  change D*(∫ y, J y) = -(α.val+1)*(∫ y, I y)
  linarith
end Real
