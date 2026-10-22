/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Polynomial
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Values

/-! # Reflection of weighted power-law modes

Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

public section
open Set MeasureTheory Polynomial
namespace Real


end Real

namespace Real
/-- Reflection exchanges the two restrictions of an integrable power-law input. -/
theorem powerLawRight_eq_left_reflect {α : ℝ} (x : Icc (-1 : ℝ) 1) (f : PowerLawInput α x.val) :
    powerLawRight (f.right x) = powerLawLeft
      (f.reflect.left ⟨-x.val,by constructor <;> linarith [x.property.1,x.property.2]⟩) := by
  let xn : Icc (-1 : ℝ) 1 := ⟨-x.val,by constructor <;> linarith [x.property.1,x.property.2]⟩
  obtain ⟨F,he,_,_⟩ := f.exists_weightedIntervalRepresentative
  have hr : powerLawRight (f.right x) = ∫ y in x.val..1, F y := by
    unfold powerLawRight
    have h (y : Ioo x.val (1 : ℝ)) :
        (y.val-x.val)^α*(f.right x).val y = F y.val := by
      let z : PowerLawDomain x.val :=
        ⟨y.val,⟨x.property.1.trans_lt y.property.1,y.property.2⟩,y.property.1.ne'⟩
      change (y.val-x.val)^α*f.val z = F z.val
      rw [he,abs_of_neg (sub_neg.mpr y.property.1),neg_sub]
    simp_rw [h]
    rw [integral_subtype_comap (μ := volume) measurableSet_Ioo F,
      intervalIntegral.integral_of_le x.property.2,integral_Ioc_eq_integral_Ioo]
  have hl : powerLawLeft (f.reflect.left xn) = ∫ y in (-1 : ℝ)..(-x.val), F (-y) := by
    unfold powerLawLeft
    have h (y : Ioo (-1 : ℝ) xn.val) :
        (xn.val-y.val)^α*(f.reflect.left xn).val y = F (-y.val) := by
      let z : PowerLawDomain x.val := ⟨-y.val,
        by constructor <;> dsimp only [xn] at * <;> linarith [y.property.1,y.property.2,x.property.1,x.property.2],
        by dsimp only [xn] at *; linarith [y.property.2]⟩
      change (-x.val-y.val)^α*f.val z = F z.val
      rw [he]
      have hh : |x.val-z.val| = -x.val-y.val := by
        change |x.val-(-y.val)| = -x.val-y.val
        rw [abs_of_neg (by dsimp only [xn] at *; linarith [y.property.2])]
        ring
      rw [hh]
    simp_rw [h]
    rw [integral_subtype_comap (μ := volume) measurableSet_Ioo (fun y ↦ F (-y)),
      intervalIntegral.integral_of_le xn.property.1,integral_Ioc_eq_integral_Ioo]
  change powerLawRight (f.right x) = powerLawLeft (f.reflect.left xn)
  rw [hr,hl,intervalIntegral.integral_comp_neg]
  simp only [neg_neg]

/-- Reflection of a Gegenbauer mode introduces its parity sign. -/
theorem powerLawRight_gegenbauerMode_reflect (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (n : ℕ) :
    powerLawRight ((PowerLawInput.gegenbauerMode α lam x n).right
      ⟨x.val,Ioo_subset_Icc_self x.property⟩) = (-1 : ℝ)^n *
      powerLawLeftPolynomial α lam
        ⟨-x.val,by constructor <;> linarith [x.property.1,x.property.2]⟩ (gegenbauer lam.val n) := by
  rw [powerLawRight_eq_left_reflect,powerLawLeftPolynomial_apply]
  unfold powerLawLeft
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change (-x.val-y.val)^α.val*((gegenbauerWeight lam.val ⟨-y.val,_⟩ : ℝ)*
      (gegenbauer lam.val n).eval (-y.val)) = _
  rw [PowerLawLeftInput.gegenbauerPolynomial_apply,eval_gegenbauer_neg]
  have hw : (gegenbauerWeight lam.val ⟨-y.val,by constructor <;> linarith [y.property.1,y.property.2,x.property.1,x.property.2]⟩ : ℝ) =
      (gegenbauerWeight lam.val ⟨y.val,by constructor <;> linarith [y.property.1,y.property.2,x.property.1,x.property.2]⟩ : ℝ) := by
    simp only [gegenbauerWeight_apply,neg_sq]
  rw [hw]
  ring
end Real
