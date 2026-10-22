/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.WeightedDerivative

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalWeighted

/-! # Polynomial input maps for power-law integration

Exact linear functionals, with all integrability discharged in the natural
parameter range. Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open Set MeasureTheory Polynomial
namespace Real

/-- Polynomial inputs for the classical left kernel. -/
def PowerLawLeftInput.gegenbauerPolynomial (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (p : ℝ[X]) :
    PowerLawLeftInput α.val ⟨x.val,x.property.1.le⟩ :=
  PowerLawInput.left ⟨x.val,Ioo_subset_Icc_self x.property⟩
    (.gegenbauerContinuous α lam x ⟨fun y ↦ p.eval y.val,p.continuous.comp continuous_subtype_val⟩)

theorem PowerLawLeftInput.gegenbauerPolynomial_apply (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (p : ℝ[X])
    (y : Ioo (-1 : ℝ) x.val) :
    (PowerLawLeftInput.gegenbauerPolynomial α lam x p).val y =
      (Polynomial.gegenbauerWeight lam.val ⟨y.val,y.property.1,y.property.2.trans x.property.2⟩ : ℝ)*
        p.eval y.val := rfl

def powerLawLeftPolynomial (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := powerLawLeft (.gegenbauerPolynomial α lam x p)
  map_add' p q := by
    have hp := (PowerLawLeftInput.gegenbauerPolynomial α lam x p).property
    have hq := (PowerLawLeftInput.gegenbauerPolynomial α lam x q).property
    simpa only [powerLawLeft,PowerLawLeftInput.gegenbauerPolynomial,PowerLawInput.left,
      PowerLawInput.gegenbauerContinuous,ContinuousMap.coe_mk,eval_add,mul_add] using integral_add hp hq
  map_smul' c p := by
    change powerLawLeft (.gegenbauerPolynomial α lam x (c • p)) =
      c*powerLawLeft (.gegenbauerPolynomial α lam x p)
    unfold powerLawLeft PowerLawLeftInput.gegenbauerPolynomial PowerLawInput.left
      PowerLawInput.gegenbauerContinuous
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [ContinuousMap.coe_mk,eval_smul,smul_eq_mul]
    ring

theorem powerLawLeftPolynomial_apply (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (p : ℝ[X]) :
    powerLawLeftPolynomial α lam x p = powerLawLeft (.gegenbauerPolynomial α lam x p) := rfl




end Real

namespace Real
/-- A polynomial factor shifts the classical open-domain weight. -/
theorem powerLawLeftPolynomial_shift_weight (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (p : ℝ[X]) :
    powerLawLeftPolynomial α lam x ((1-X^2)*p) =
      powerLawLeftPolynomial α
        ⟨lam.val+1,by change -(1/2 : ℝ) < lam.val+1; linarith [show -(1/2 : ℝ) < lam.val from lam.property]⟩ x p := by
  rw [powerLawLeftPolynomial_apply, powerLawLeftPolynomial_apply]
  unfold powerLawLeft
  apply integral_congr_ae
  filter_upwards [] with y
  rw [PowerLawLeftInput.gegenbauerPolynomial_apply,
    PowerLawLeftInput.gegenbauerPolynomial_apply]
  rw [gegenbauerWeight_add_one]
  simp only [eval_mul,eval_sub,eval_one,eval_pow,eval_X]
  ring

/-- Multiplication by the coordinate shifts the left kernel exponent. -/
theorem powerLawLeftPolynomial_mul_X (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (p : ℝ[X]) :
    powerLawLeftPolynomial α lam x (X*p) =
      x.val*powerLawLeftPolynomial α lam x p -
      powerLawLeftPolynomial
        ⟨α.val+1,by change -1 < α.val+1; linarith [show -1 < α.val from α.property]⟩ lam x p := by
  let α' : Ioi (-1 : ℝ) := ⟨α.val+1,by change -1 < α.val+1; linarith [show -1 < α.val from α.property]⟩
  have hi := (PowerLawLeftInput.gegenbauerPolynomial α lam x p).property
  have hj := (PowerLawLeftInput.gegenbauerPolynomial α' lam x p).property
  rw [powerLawLeftPolynomial_apply, powerLawLeftPolynomial_apply,
    powerLawLeftPolynomial_apply]
  unfold powerLawLeft
  rw [← integral_const_mul, ← integral_sub (hi.const_mul x.val) hj]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [PowerLawLeftInput.gegenbauerPolynomial_apply,
    PowerLawLeftInput.gegenbauerPolynomial_apply,
    PowerLawLeftInput.gegenbauerPolynomial_apply]
  simp only [eval_mul,eval_X]
  have hb : 0 < x.val-y.val := sub_pos.mpr y.property.2
  rw [rpow_add_one hb.ne']
  ring
end Real
