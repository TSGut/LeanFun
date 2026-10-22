/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.EquioscillationCharacterization

/-! # Uniqueness of real uniform polynomial approximation
Apply equioscillation to the midpoint of two minimizers. Reference: ATAP,
Theorem 10.1 and Exercise 10.10.
-/

public section
namespace Polynomial
open Set

/-- A continuous real function has at most one best degree-`n` polynomial
on a nondegenerate compact interval (ATAP 10.1). -/
theorem bestApproximation_unique {a b : ℝ} (hab : a < b) {n : ℕ}
    (f : C(Icc a b, ℝ)) {p q : ℝ[X]} (hp : p.degree ≤ n) (hq : q.degree ≤ n)
    (hpmin : ∀ r : ℝ[X], r.degree ≤ n →
      ‖f - p.toContinuousMapOn (Icc a b)‖ ≤ ‖f - r.toContinuousMapOn (Icc a b)‖)
    (hqmin : ∀ r : ℝ[X], r.degree ≤ n →
      ‖f - q.toContinuousMapOn (Icc a b)‖ ≤ ‖f - r.toContinuousMapOn (Icc a b)‖) : p = q := by
  let r : ℝ[X] := (1 / 2 : ℝ) • (p + q)
  let E := ‖f - p.toContinuousMapOn (Icc a b)‖
  have hE : 0 ≤ E := norm_nonneg _
  have hEq : ‖f - q.toContinuousMapOn (Icc a b)‖ = E :=
    le_antisymm (hqmin p hp) (hpmin q hq)
  have hr : r.degree ≤ n := (degree_smul_le _ _).trans ((degree_add_le _ _).trans (max_le hp hq))
  have hb (x : Icc a b) : |f x - p.eval (x : ℝ)| ≤ E ∧ |f x - q.eval (x : ℝ)| ≤ E := by
    constructor
    · exact (f - p.toContinuousMapOn (Icc a b)).norm_coe_le_norm x
    · exact ((f - q.toContinuousMapOn (Icc a b)).norm_coe_le_norm x).trans_eq hEq
  have heval (x : ℝ) : r.eval x = (p.eval x + q.eval x) / 2 := by simp [r, div_eq_mul_inv]; ring
  have hrle : ‖f - r.toContinuousMapOn (Icc a b)‖ ≤ E := by
    apply (ContinuousMap.norm_le _ hE).2
    intro x
    change |f x - r.eval (x : ℝ)| ≤ E
    rw [heval, abs_le]
    have h1 := abs_le.mp (hb x).1
    have h2 := abs_le.mp (hb x).2
    constructor <;> linarith
  have hreq : ‖f - r.toContinuousMapOn (Icc a b)‖ = E := le_antisymm hrle (hpmin r hr)
  have hrmin (s : ℝ[X]) (hs : s.degree ≤ n) :
      ‖f - r.toContinuousMapOn (Icc a b)‖ ≤ ‖f - s.toContinuousMapOn (Icc a b)‖ :=
    hrle.trans (hpmin s hs)
  obtain ⟨x, σ, hx, hσ, he⟩ := equioscillates_of_bestApproximation hab f hr hrmin
  have hxabs (i : Fin (n + 2)) : |f (x i) - r.eval (x i : ℝ)| = E := by
    have h := congrArg abs (he i)
    simpa only [ContinuousMap.sub_apply, toContinuousMapOn_apply, toContinuousMap_apply,
      abs_mul, hσ, abs_neg_one_pow, one_mul, hreq, abs_of_nonneg hE] using h
  have hsame (i : Fin (n + 2)) : p.eval (x i : ℝ) = q.eval (x i : ℝ) := by
    have h1 := abs_le.mp (hb (x i)).1
    have h2 := abs_le.mp (hb (x i)).2
    have ht := hxabs i
    rw [heval] at ht
    rcases abs_eq (by exact hE) |>.mp ht with h | h <;> linarith
  apply eq_of_natDegree_lt_card_of_eval_eq p q (fun _ _ h ↦ hx.injective (Subtype.ext h)) hsame
  simpa only [Fintype.card_fin, max_lt_iff] using
    And.intro ((natDegree_le_of_degree_le hp).trans_lt (show n < n + 2 by omega))
      ((natDegree_le_of_degree_le hq).trans_lt (show n < n + 2 by omega))

end Polynomial
