/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ParameterShiftMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalModification
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Coordinates

import Mathlib.Topology.Algebra.Polynomial

/-! # Support bounds for all Proriol parameter shifts
Integer raising controls both total-degree and inner-index bandwidth.
Reference: DLMF 18.37.7–8 and separated measure modification.
-/

public section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- Inner parameter shifts bound the inner-index gap independently of outer parameters. -/
theorem integralInner_proriol_shift_eq_zero_of_inner_gap {η β γ : ℝ}
    (hη : -1 < η) (hβ : -1 < β) (hγ : -1 < γ) (α α' : ℝ) (b c : ℕ)
    (n k m j : ℕ) (hkj : k < j ∨ j+(b+c) < k) :
    integralInner (proriolMeasure η (β+b) (γ+c)) (IntegrablePair.of (proriolMeasure η (β+b) (γ+c)) (proriol α β γ n k) (proriol α' (β+b) (γ+c) m j) (h := (hasFiniteMoments_proriolMeasure hη (by have := Nat.cast_nonneg (α := ℝ) b; linarith) (by have := Nat.cast_nonneg (α := ℝ) c; linarith)).integrable_mul _ _)) = 0 := by
  have hb : -1 < β+b := by linarith [Nat.cast_nonneg (α := ℝ) b]
  have hc : -1 < γ+c := by linarith [Nat.cast_nonneg (α := ℝ) c]
  let := isFiniteMeasure_unitJacobiMeasure hη (show -1 < (β+b)+(γ+c)+1 by linarith)
  let := isFiniteMeasure_unitJacobiMeasure hb hc
  rw [integralInner, integral_proriolMeasure _ _ _ ⟨_, (hasFiniteMoments_proriolProductMeasure hη hb hc).integrable_mul _ _⟩]
  simp only
  apply mul_eq_zero_of_right
  have hi := (koornwinderMeasure_integral_univ (fun x => x) continuous_id
    (unitJacobiMeasure η ((β+b)+(γ+c)+1)) (unitJacobiMeasure (β+b) (γ+c))
    ⟨fun v ↦ eval v (proriol α β γ n k * proriol α' (β+b) (γ+c) m j), by
      simpa only [proriolProductMeasure, map_one, mul_one] using
        (hasFiniteMoments_proriolProductMeasure hη hb hc).integrable_mul (proriol α β γ n k * proriol α' (β+b) (γ+c) m j) 1⟩).2
  simp only [map_mul] at hi
  rw [proriolProductMeasure, hi]
  have he : (∫ v, eval ((![v.1, v.1*v.2] : Fin 2 → ℝ)) (proriol α β γ n k) *
      eval ((![v.1, v.1*v.2] : Fin 2 → ℝ)) (proriol α' (β+b) (γ+c) m j)
      ∂(unitJacobiMeasure η ((β+b)+(γ+c)+1)).prod (unitJacobiMeasure (β+b) (γ+c))) =
      (∫ x, (shiftedJacobi α (β+γ+2*k+1) (n-k)).eval x *
        (shiftedJacobi α' ((β+b)+(γ+c)+2*j+1) (m-j)).eval x * x^(k+j)
        ∂unitJacobiMeasure η ((β+b)+(γ+c)+1)) *
      Polynomial.integralInner (unitJacobiMeasure (β+b) (γ+c)) (Polynomial.IntegrablePair.of (unitJacobiMeasure (β+b) (γ+c)) (shiftedJacobi β γ k) (shiftedJacobi (β+b) (γ+c) j)) := by
    rw [Polynomial.integralInner, ← integral_prod_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [eval_proriol_scaled, eval_proriol_scaled, pow_add]
    ring
  rw [he, integralInner_shiftedJacobi_add_nat_eq_zero hβ hγ b c k j hkj, mul_zero]

/-- Combined shifts have both total-degree and inner-index support bounds. -/
theorem integralInner_proriol_shift_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (a b c : ℕ)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hgap : (k < j ∨ j+(b+c) < k) ∨ (n < m ∨ m+(a+b+c) < n)) :
    integralInner (proriolMeasure (α+a) (β+b) (γ+c)) (IntegrablePair.of (proriolMeasure (α+a) (β+b) (γ+c)) (proriol α β γ n k) (proriol (α+a) (β+b) (γ+c) m j) (h := (hasFiniteMoments_proriolMeasure (by have := Nat.cast_nonneg (α := ℝ) a; linarith) (by have := Nat.cast_nonneg (α := ℝ) b; linarith) (by have := Nat.cast_nonneg (α := ℝ) c; linarith)).integrable_mul _ _)) = 0 := by
  rcases hgap with h | h
  · exact integralInner_proriol_shift_eq_zero_of_inner_gap
      (by linarith [Nat.cast_nonneg (α := ℝ) a]) hβ hγ _ _ b c n k m j h
  · exact integralInner_proriol_shift_eq_zero_of_total_gap hα hβ hγ a b c hk hj h

/-- Actual finite Proriol connection coordinates obey both support bounds. -/
theorem proriol_connection_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (a b c N : ℕ)
    (hαa : -1 < α+a) (hβb : -1 < β+b) (hγc : -1 < γ+c)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N})
    (hgap : (i.1 1 < j.1 1 ∨ j.1 1+(b+c) < i.1 1) ∨
      (i.1 0+i.1 1 < j.1 0+j.1 1 ∨ j.1 0+j.1 1+(a+b+c) < i.1 0+i.1 1)) :
    (proriolDegreeBasis hαa hβb hγc N).repr (proriolDegreeBasis hα hβ hγ N i) j = 0 := by
  rw [proriolDegreeBasis_repr]
  simp only [proriolDegreeBasis_apply]
  rw [integralInner_proriol_shift_eq_zero hα hβ hγ a b c (by omega) (by omega) hgap, zero_div]

end MvPolynomial
