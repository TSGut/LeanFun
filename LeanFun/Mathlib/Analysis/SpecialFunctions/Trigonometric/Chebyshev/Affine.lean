/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp

/-! # Affine transport from the Chebyshev interval
The canonical polynomial families and transforms stay on `[-1,1]`. Affine
coordinates transport their approximation, differentiation, and integration to
`[a,b]`. Reference: Chebfun's interval scaling; ATAP, Chapters 6 and 19.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open Set MeasureTheory

/-- The affine map from `[-1,1]` to `[a,b]` used for Chebfun interval scaling. -/
noncomputable def intervalMap (a b t : ℝ) : ℝ := (b - a) / 2 * t + (a + b) / 2

/-- The canonical Chebyshev coordinate on `[a,b]`, inverse when `a ≠ b`. -/
noncomputable def intervalCoord (a : ℝ) (b : {b : ℝ // a ≠ b}) (x : ℝ) : ℝ :=
  (2 * x - (a + b.val)) / (b.val - a)

@[simp] theorem intervalMap_neg_one (a b : ℝ) : intervalMap a b (-1) = a := by
  unfold intervalMap
  ring

@[simp] theorem intervalMap_one (a b : ℝ) : intervalMap a b 1 = b := by
  unfold intervalMap
  ring

/-- Physical and canonical coordinates cancel for a nondegenerate interval. -/
@[simp] theorem intervalMap_intervalCoord {a b : ℝ} (hab : a < b) (x : ℝ) :
    intervalMap a b (intervalCoord a ⟨b, ne_of_lt hab⟩ x) = x := by
  unfold intervalMap intervalCoord
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

/-- Canonical and physical coordinates cancel for a nondegenerate interval. -/
@[simp] theorem intervalCoord_intervalMap {a b : ℝ} (hab : a < b) (t : ℝ) :
    intervalCoord a ⟨b, ne_of_lt hab⟩ (intervalMap a b t) = t := by
  unfold intervalMap intervalCoord
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

/-- The forward map preserves closed-interval membership. -/
theorem intervalMap_mem_Icc {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc (-1 : ℝ) 1) :
    intervalMap a b t ∈ Icc a b := by
  unfold intervalMap
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr ht.2),
    mul_nonneg (sub_nonneg.mpr hab.le) (show 0 ≤ t + 1 by linarith [ht.1])]

/-- The inverse map preserves closed-interval membership. -/
theorem intervalCoord_mem_Icc {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    intervalCoord a ⟨b, ne_of_lt hab⟩ x ∈ Icc (-1 : ℝ) 1 := by
  unfold intervalCoord
  constructor
  · apply (le_div_iff₀ (sub_pos.mpr hab)).2
    linarith [hx.1]
  · apply (div_le_iff₀ (sub_pos.mpr hab)).2
    linarith [hx.2]

/-- Derivative of the physical coordinate map. -/
theorem hasDerivAt_intervalMap (a b t : ℝ) :
    HasDerivAt (intervalMap a b) ((b - a) / 2) t := by
  unfold intervalMap
  convert ((hasDerivAt_id t).const_mul ((b - a) / 2)).add_const ((a + b) / 2) using 1 <;> simp

/-- Derivative of the canonical coordinate, giving the factor `2/(b-a)`. -/
theorem hasDerivAt_intervalCoord (a : ℝ) (b : {b : ℝ // a ≠ b}) (x : ℝ) :
    HasDerivAt (intervalCoord a b) (2 / (b.val - a)) x := by
  unfold intervalCoord
  convert (((hasDerivAt_id x).const_mul 2).sub_const (a + b.val)).div_const (b.val - a) using 1 <;> simp

/-- Differentiation on a physical interval is scaled by `2/(b-a)`. -/
theorem hasDerivAt_comp_intervalCoord {a x d : ℝ} {b : {b : ℝ // a ≠ b}} {f : ℝ → ℝ}
    (hf : HasDerivAt f d (intervalCoord a b x)) :
    HasDerivAt (fun y ↦ f (intervalCoord a b y)) (d * (2 / (b.val - a))) x :=
  hf.comp x (hasDerivAt_intervalCoord a b x)

/-- A uniform approximation bound transports without changing its constant. -/
theorem abs_sub_comp_intervalCoord_le {a b ε : ℝ} (hab : a < b)
    {f g : ℝ → ℝ}
    (he : ∀ t ∈ Icc (-1 : ℝ) 1, |f (intervalMap a b t) - g t| ≤ ε)
    {x : ℝ} (hx : x ∈ Icc a b) : |f x - g (intervalCoord a ⟨b, ne_of_lt hab⟩ x)| ≤ ε := by
  simpa only [intervalMap_intervalCoord hab] using he _ (intervalCoord_mem_Icc hab hx)

/-- Transported polynomial values are ordinary polynomial composition; no new
interval-parametrised polynomial family is introduced. -/
theorem eval_comp_intervalCoord (p : ℝ[X]) (a : ℝ) (b : {b : ℝ // a ≠ b}) (x : ℝ) :
    (p.comp (Polynomial.C (2 / (b.val - a)) * X - Polynomial.C ((a + b.val) / (b.val - a)))).eval x =
      p.eval (intervalCoord a b x) := by
  rw [eval_comp]
  congr 1
  simp only [eval_sub, eval_mul, eval_C, eval_X, intervalCoord]
  ring

/-- Nondegenerate affine transport preserves polynomial degree. -/
theorem degree_comp_intervalCoord (p : ℝ[X]) {a b : ℝ} (hab : a < b) :
    (p.comp (Polynomial.C (2 / (b - a)) * X - Polynomial.C ((a + b) / (b - a)))).degree =
      p.degree := by
  have hc : 2 / (b - a) ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt (sub_pos.mpr hab))
  have hd : (Polynomial.C (2 / (b - a)) * X -
      Polynomial.C ((a + b) / (b - a))).degree = 1 := by
    rw [degree_sub_eq_left_of_degree_lt (degree_C_lt_degree_C_mul_X hc), degree_C_mul_X hc]
  rw [degree_comp (by rw [hd]; norm_num), hd, mul_one]

/-- Classical interval-integrable real input, including either orientation and equal endpoints. -/
abbrev _root_.MeasureTheory.IntervalIntegrableInput (a b : ℝ) := {f : ℝ → ℝ // IntervalIntegrable f volume a b}

/-- Bundled interval data have genuine oriented integrals. -/
theorem _root_.MeasureTheory.IntervalIntegrableInput.integrable {a b : ℝ} (f : IntervalIntegrableInput a b) :
    IntervalIntegrable f.val volume a b := f.property

/-- Integrability transports through the affine map, including its constant case. -/
theorem intervalIntegrable_comp_intervalMap (a b : ℝ) (f : IntervalIntegrableInput a b) :
    IntervalIntegrable (fun t ↦ f.val (intervalMap a b t)) volume (-1) 1 := by
  by_cases hab : a = b
  · subst b
    simp [intervalMap]
  have h := (f.property.comp_add_right ((a + b) / 2)).comp_mul_left (c := (b - a) / 2)
  have ha : (a - (a + b) / 2) / ((b - a) / 2) = -1 := by
    field_simp [sub_ne_zero.mpr (Ne.symm hab)]; ring
  have hb : (b - (a + b) / 2) / ((b - a) / 2) = 1 := by
    field_simp [sub_ne_zero.mpr (Ne.symm hab)]; ring
  simpa only [ha, hb, intervalMap] using h

/-- The classical oriented change of variables for integrable input. -/
theorem integral_comp_intervalMap (a b : ℝ) (f : IntervalIntegrableInput a b) :
    (∫ x in a..b, f.val x) =
      (b - a) / 2 * ∫ t in (-1 : ℝ)..1, f.val (intervalMap a b t) := by
  have h := intervalIntegral.smul_integral_comp_mul_add
    (a := (-1 : ℝ)) (b := 1) f.val ((b - a) / 2) ((a + b) / 2)
  have h₀ : (b - a) / 2 * (-1) + (a + b) / 2 = a := by ring
  have h₁ : (b - a) / 2 * 1 + (a + b) / 2 = b := by ring
  simpa only [h₀, h₁, smul_eq_mul, intervalMap] using h.symm

end Polynomial.Chebyshev
