/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.CoerciveSections
public import Mathlib.Tactic.NoncommRing
@[expose] public noncomputable section
/-! # Sign changes in finite sections

The unresolved complement remains the identity when an operator is negated.
The involution I-2P transfers invertibility and projected solutions correctly.
Reference: the finite-section method of Böttcher--Silbermann.
-/

namespace ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem reflection_square (P : E →L[ℝ] E) (hP : P*P=P) :
    (1-2*P)*(1-2*P) = 1 := by noncomm_ring [hP]
private theorem reflection_unit (P : E →L[ℝ] E) (hP : P*P=P) :
    IsUnit (1-2*P) := isUnit_iff_exists.mpr ⟨_,reflection_square P hP,reflection_square P hP⟩
private theorem reflection_inverse (P : E →L[ℝ] E) (hP : P*P=P) :
    Ring.inverse (1-2*P) = 1-2*P := by
  calc
    _ = Ring.inverse (1-2*P) * ((1-2*P)*(1-2*P)) := by rw [reflection_square P hP,mul_one]
    _ = 1-2*P := Ring.inverse_mul_cancel_left _ _ (reflection_unit P hP)
/-- Negating the resolved operator multiplies its section by the coordinate reflection. -/
theorem coerciveFiniteSection_neg (P A : E →L[ℝ] E) (hP : P*P=P) :
    coerciveFiniteSection P (-A) = (1-2*P)*coerciveFiniteSection P A := by
  change 1-P+P*(-A*P) = (1-2*P)*(1-P+P*(A*P))
  have hPA : P*(P*(A*P)) = P*(A*P) := by rw [← mul_assoc, hP]
  noncomm_ring [hP,hPA]
/-- A sign change preserves finite-section invertibility. -/
theorem isUnit_coerciveFiniteSection_neg_iff (P A : E →L[ℝ] E) (hP : P*P=P) :
    IsUnit (coerciveFiniteSection P (-A)) ↔ IsUnit (coerciveFiniteSection P A) := by
  constructor
  · intro h
    have hh := (reflection_unit P hP).mul h
    rw [coerciveFiniteSection_neg P A hP, ← mul_assoc,reflection_square P hP,one_mul] at hh
    exact hh
  · intro h
    rw [coerciveFiniteSection_neg P A hP]
    exact (reflection_unit P hP).mul h
/-- Negating both operator and projected data preserves the finite-section solution. -/
theorem inverse_coerciveFiniteSection_neg_apply (P : E →L[ℝ] E)
    (A : {A : E →L[ℝ] E // IsUnit (coerciveFiniteSection P A)})
    (hP : P*P=P) (g : E) :
    Ring.inverse (coerciveFiniteSection P (-A.val)) (-(P g)) =
      Ring.inverse (coerciveFiniteSection P A.val) (P g) := by
  rw [coerciveFiniteSection_neg P A.val hP, Ring.inverse_mul (Or.inl (reflection_unit P hP)),
    reflection_inverse P hP, mul_apply_eq_comp]
  congr 1
  have hid : P (P g) = P g := congrArg (fun B : E →L[ℝ] E ↦ B g) hP
  simp only [sub_apply, one_apply_eq_self, mul_apply_eq_comp, map_neg, hid,
    ofNat_apply]
  module
/-- Negating a full operator and its data preserves the inverse solution on the invertible domain. -/
theorem inverse_neg_apply_neg (A : {A : E →L[ℝ] E // IsUnit A}) (g : E) :
    Ring.inverse (-A.val) (-g) = Ring.inverse A.val g := by
  have hn : Ring.inverse (-1 : E →L[ℝ] E) = -1 := by
    have h := reflection_inverse (1 : E →L[ℝ] E) (by simp)
    norm_num at h
    exact h
  rw [show -A.val = (-1)*A.val by simp, Ring.inverse_mul (Or.inl isUnit_neg_one), hn,
    mul_apply_eq_comp, neg_apply, one_apply_eq_self, neg_neg]
/-- Sign reversal preserves the full solution equation, including singular operators. -/
theorem neg_apply_eq_neg_iff (A : E →L[ℝ] E) (u g : E) :
    (-A) u = -g ↔ A u = g := by simp

/-- Sign reversal preserves projected solution equations, including singular sections. -/
theorem coerciveFiniteSection_neg_apply_eq_iff (P A : E →L[ℝ] E)
    (hP : P * P = P) (u g : E) :
    coerciveFiniteSection P (-A) u = -(P g) ↔
      coerciveFiniteSection P A u = P g := by
  have hid : P (P g) = P g := congrArg (fun B : E →L[ℝ] E ↦ B g) hP
  have hr : (1-2*P : E →L[ℝ] E) (P g) = -(P g) := by
    simp only [sub_apply, one_apply_eq_self, mul_apply_eq_comp, hid, ofNat_apply]
    module
  rw [coerciveFiniteSection_neg P A hP, mul_apply_eq_comp, ← hr]
  constructor
  · intro h
    have hh := congrArg (fun x ↦ (1-2*P : E →L[ℝ] E) x) h
    simpa only [← mul_apply_eq_comp, ← mul_assoc, reflection_square P hP, one_mul, one_apply_eq_self] using hh
  · exact congrArg _
end ContinuousLinearMap
