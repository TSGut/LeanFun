/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.StandardMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.TotalDegree
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Polynomial measure modification in the Proriol family
Raising alpha by a nonnegative integer multiplies the triangle weight by
(1-x)^r. Reference: DLMF 18.37.8 and polynomial measure modification.
-/

public section
open MeasureTheory Polynomial Set
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- Raising the outer parameter is the polynomial density change (1-x)^r. -/
theorem integral_proriolMeasure_alpha_add_nat {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (r : ℕ)
    (p : MvPolynomial (Fin 2) ℝ) :
    ∫ v, eval v p ∂proriolMeasure (α+r) β γ =
      ∫ v, eval v ((1-X 0)^r*p) ∂proriolMeasure α β γ := by
  rw [integral_proriolMeasure_density (by linarith [Nat.cast_nonneg (α := ℝ) r]) hβ hγ,
    integral_proriolMeasure_density hα hβ hγ]
  simp only [map_mul, map_pow, map_sub, map_one, eval_X, Matrix.cons_val_zero]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Real.rpow_add (by linarith [x.property.2] : 0 < 1-(x : ℝ)), Real.rpow_natCast]
  have he (y : Set.Ioo (0 : ℝ) (x : ℝ)) : ((x : ℝ)-(y : ℝ))^β * (y : ℝ)^γ * ((1-(x : ℝ))^r * eval (![(x : ℝ),(y : ℝ)] : Fin 2 → ℝ) p) =
      (1-(x : ℝ))^r * (((x : ℝ)-(y : ℝ))^β * (y : ℝ)^γ * eval (![(x : ℝ),(y : ℝ)] : Fin 2 → ℝ) p) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  ring

/-- Pairing form of the alpha shift; it is the exact modified Gram identity. -/
theorem integralInner_proriolMeasure_alpha_add_nat {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (r : ℕ)
    (p q : MvPolynomial (Fin 2) ℝ) :
    integralInner (proriolMeasure (α+r) β γ) (IntegrablePair.of (proriolMeasure (α+r) β γ) p q (h := (hasFiniteMoments_proriolMeasure (by have := Nat.cast_nonneg (α := ℝ) r; linarith) hβ hγ).integrable_mul _ _)) =
      integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) ((1-X 0)^r*p) q) := by
  have he := integral_proriolMeasure_alpha_add_nat hα hβ hγ r (p*q)
  simpa only [map_mul, integralInner, mul_assoc] using he

/-- Lower-degree orthogonality also holds for the standard triangle measure. -/
theorem integralInner_proriolMeasure_eq_zero_of_totalDegree_lt {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (q : MvPolynomial (Fin 2) ℝ)
    {m j : ℕ} (hj : j ≤ m) (hq : q.totalDegree < m) :
    integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) q (proriol α β γ m j)) = 0 := by
  rw [integralInner, integral_proriolMeasure _ _ _ ⟨_, (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul _ _⟩]
  change _ * integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) q _) = 0
  rw [integralInner_proriol_eq_zero_of_totalDegree_lt hα hβ hγ q hj hq, mul_zero]

/-- Alpha-raising connection pairings have total-degree bandwidth r. -/
theorem integralInner_proriol_alpha_shift_eq_zero_of_total_gap {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (r : ℕ)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m) (hgap : n < m ∨ m+r < n) :
    integralInner (proriolMeasure (α+r) β γ) (IntegrablePair.of (proriolMeasure (α+r) β γ) (proriol α β γ n k) (proriol (α+r) β γ m j) (h := (hasFiniteMoments_proriolMeasure (by have := Nat.cast_nonneg (α := ℝ) r; linarith) hβ hγ).integrable_mul _ _)) = 0 := by
  rcases hgap with h | h
  · exact integralInner_proriolMeasure_eq_zero_of_totalDegree_lt
      (by linarith [Nat.cast_nonneg (α := ℝ) r]) hβ hγ _ hj
      ((totalDegree_proriol_le α β γ hk).trans_lt h)
  · rw [integralInner_comm, integralInner_proriolMeasure_alpha_add_nat hα hβ hγ]
    apply integralInner_proriolMeasure_eq_zero_of_totalDegree_lt hα hβ hγ _ hk
    apply lt_of_le_of_lt ((totalDegree_mul _ _).trans ?_) h
    have hd : ((1-X 0 : MvPolynomial (Fin 2) ℝ)^r).totalDegree ≤ r := by
      exact (totalDegree_pow _ _).trans (by
        have ht : (1-X 0 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 :=
          (totalDegree_sub _ _).trans (by simp)
        simpa using Nat.mul_le_mul_left r ht)
    have hp := totalDegree_proriol_le (α+r) β γ hj
    omega

end MvPolynomial
