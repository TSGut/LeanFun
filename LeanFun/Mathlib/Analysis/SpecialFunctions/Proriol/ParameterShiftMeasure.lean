/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.MeasureModification
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # The three polynomial density shifts on a Proriol triangle
Integer parameter shifts multiply the weight by the corresponding barycentric
coordinate powers. Reference: DLMF 18.37.8.
-/

@[expose] public section
open MeasureTheory Polynomial Set
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- The polynomial density for simultaneous nonnegative integer parameter shifts. -/
noncomputable def proriolShiftDensity (a b c : ℕ) : MvPolynomial (Fin 2) ℝ :=
  (1-X 0)^a * (X 0-X 1)^b * X 1^c

/-- The degree of the modifying density is bounded by the sum of the shifts. -/
theorem totalDegree_proriolShiftDensity_le (a b c : ℕ) :
    (proriolShiftDensity a b c).totalDegree ≤ a+b+c := by
  have hx : (1-X 0 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (by simp)
  have hy : (X 0-X 1 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (by simp)
  have ha : ((1-X 0 : MvPolynomial (Fin 2) ℝ)^a).totalDegree ≤ a :=
    (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left a hx)
  have hb : ((X 0-X 1 : MvPolynomial (Fin 2) ℝ)^b).totalDegree ≤ b :=
    (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left b hy)
  have hc : ((X 1 : MvPolynomial (Fin 2) ℝ)^c).totalDegree ≤ c := by simp
  exact (totalDegree_mul _ _).trans
    (Nat.add_le_add ((totalDegree_mul _ _).trans (Nat.add_le_add ha hb)) hc)

/-- All three integer shifts are exact polynomial density changes on polynomial integrals. -/
theorem integral_proriolMeasure_add_nat {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (a b c : ℕ)
    (p : MvPolynomial (Fin 2) ℝ) :
    ∫ v, eval v p ∂proriolMeasure (α+a) (β+b) (γ+c) =
      ∫ v, eval v (proriolShiftDensity a b c*p) ∂proriolMeasure α β γ := by
  rw [integral_proriolMeasure_density
    (by linarith [Nat.cast_nonneg (α := ℝ) a])
    (by linarith [Nat.cast_nonneg (α := ℝ) b])
    (by linarith [Nat.cast_nonneg (α := ℝ) c]), integral_proriolMeasure_density hα hβ hγ]
  simp only [proriolShiftDensity, map_mul, map_pow, map_sub, map_one, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Real.rpow_add (by linarith [x.property.2] : 0 < 1-(x : ℝ)), Real.rpow_natCast, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Real.rpow_add (by linarith [y.property.2] : 0 < (x : ℝ)-(y : ℝ)), Real.rpow_natCast,
    Real.rpow_add y.property.1, Real.rpow_natCast]
  ring

/-- The simultaneous parameter shift gives the exact polynomial Gram pairing identity. -/
theorem integralInner_proriolMeasure_add_nat {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (a b c : ℕ)
    (p q : MvPolynomial (Fin 2) ℝ) :
    integralInner (proriolMeasure (α+a) (β+b) (γ+c)) (IntegrablePair.of (proriolMeasure (α+a) (β+b) (γ+c)) p q (h := (hasFiniteMoments_proriolMeasure (by have := Nat.cast_nonneg (α := ℝ) a; linarith) (by have := Nat.cast_nonneg (α := ℝ) b; linarith) (by have := Nat.cast_nonneg (α := ℝ) c; linarith)).integrable_mul _ _)) =
      integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) (proriolShiftDensity a b c*p) q) := by
  have he := integral_proriolMeasure_add_nat hα hβ hγ a b c (p*q)
  simpa only [map_mul, integralInner, mul_assoc] using he

/-- Total-degree support for arbitrary nonnegative integer parameter shifts. -/
theorem integralInner_proriol_shift_eq_zero_of_total_gap {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (a b c : ℕ)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m) (hgap : n < m ∨ m+(a+b+c) < n) :
    integralInner (proriolMeasure (α+a) (β+b) (γ+c)) (IntegrablePair.of (proriolMeasure (α+a) (β+b) (γ+c)) (proriol α β γ n k) (proriol (α+a) (β+b) (γ+c) m j) (h := (hasFiniteMoments_proriolMeasure (by have := Nat.cast_nonneg (α := ℝ) a; linarith) (by have := Nat.cast_nonneg (α := ℝ) b; linarith) (by have := Nat.cast_nonneg (α := ℝ) c; linarith)).integrable_mul _ _)) = 0 := by
  rcases hgap with h | h
  · exact integralInner_proriolMeasure_eq_zero_of_totalDegree_lt
      (by linarith [Nat.cast_nonneg (α := ℝ) a])
      (by linarith [Nat.cast_nonneg (α := ℝ) b])
      (by linarith [Nat.cast_nonneg (α := ℝ) c]) _ hj
      ((totalDegree_proriol_le α β γ hk).trans_lt h)
  · rw [integralInner_comm, integralInner_proriolMeasure_add_nat hα hβ hγ]
    apply integralInner_proriolMeasure_eq_zero_of_totalDegree_lt hα hβ hγ _ hk
    apply lt_of_le_of_lt ((totalDegree_mul _ _).trans ?_) h
    have hd := totalDegree_proriolShiftDensity_le a b c
    have hp := totalDegree_proriol_le (α+a) (β+b) (γ+c) hj
    omega

end MvPolynomial
