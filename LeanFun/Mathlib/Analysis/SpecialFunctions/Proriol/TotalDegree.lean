/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Basis

/-! # Degree orthogonality and multiplication blocks for Proriol polynomials
Completeness converts pairwise orthogonality to orthogonality against every
lower-degree polynomial. Reference: multivariate three-term structure, DLMF 18.37.
-/

public section
open MeasureTheory
namespace MvPolynomial

/-- A Proriol polynomial is orthogonal to every polynomial of smaller total degree. -/
theorem integralInner_proriol_eq_zero_of_totalDegree_lt {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (q : MvPolynomial (Fin 2) ℝ)
    {m j : ℕ} (hj : j ≤ m) (hq : q.totalDegree < m) :
    integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) q (proriol α β γ m j)) = 0 := by
  classical
  let N := q.totalDegree
  let b := proriolDegreeBasis hα hβ hγ N
  let q' : restrictTotalDegree (Fin 2) ℝ N :=
    ⟨q, (mem_restrictTotalDegree _ _ _).mpr le_rfl⟩
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  have he : q = ∑ d, b.repr q' d • proriol α β γ (d.1 0+d.1 1) (d.1 1) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul, b, proriolDegreeBasis_apply, q'] using
      (congrArg (fun r : restrictTotalDegree (Fin 2) ℝ N ↦ (r : MvPolynomial (Fin 2) ℝ))
        (b.sum_repr q')).symm
  let B := integralBilinForm (proriolProductMeasure α β γ)
    (hasFiniteMoments_proriolProductMeasure hα hβ hγ)
  change B q (proriol α β γ m j) = 0
  rw [he, map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro d _
  rw [map_smul, LinearMap.smul_apply]
  change _ * integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) (proriol α β γ (d.1 0+d.1 1) (d.1 1)) (proriol α β γ m j)) = 0
  rw [integralInner_proriol_eq_zero hα hβ hγ (by omega) hj, mul_zero]
  intro h
  have hd : d.1 0+d.1 1 ≤ N := by simpa only [sum_exponents_fin_two] using d.2
  have hn := congrArg Prod.fst h
  dsimp at hn
  omega

/-- Coordinate multiplication has only three total-degree block diagonals. -/
theorem integralInner_X_mul_proriol_eq_zero_of_total_gap {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ)
    (coord : Fin 2) {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hgap : n+1 < m ∨ m+1 < n) :
    integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) (X coord * proriol α β γ n k) (proriol α β γ m j)) = 0 := by
  have hd (a b : ℕ) (hb : b ≤ a) :
      (X coord * proriol α β γ a b).totalDegree ≤ a+1 := by
    exact (totalDegree_mul _ _).trans
      ((Nat.add_le_add (le_of_eq (totalDegree_X coord)) (totalDegree_proriol_le α β γ hb)).trans (by omega))
  rcases hgap with h | h
  · exact integralInner_proriol_eq_zero_of_totalDegree_lt hα hβ hγ _ hj ((hd n k hk).trans_lt h)
  · rw [integralInner_mul_left_right, integralInner_comm]
    exact integralInner_proriol_eq_zero_of_totalDegree_lt hα hβ hγ _ hk ((hd m j hj).trans_lt h)

end MvPolynomial
