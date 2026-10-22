/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.BestApproximationUnique
public import LeanFun.Mathlib.Analysis.Normed.Module.BestApproximation
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-! # Real minimax polynomial approximation
Existence, uniqueness and equioscillation on a nondegenerate compact interval.
Reference: ATAP, Theorem 10.1.
-/

public section
namespace Polynomial
open Set

/-- Continuous real data have a minimizing real polynomial on any compact
interval. Existence alone does not require a nondegenerate interval (ATAP 10.1). -/
theorem exists_bestApproximation {a b : ℝ} (n : ℕ) (f : C(Icc a b, ℝ)) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ q : ℝ[X], q.degree ≤ n →
      ‖f - p.toContinuousMapOn (Icc a b)‖ ≤ ‖f - q.toContinuousMapOn (Icc a b)‖ := by
  let L := (toContinuousMapOnAlgHom (Icc a b)).toLinearMap.comp (degreeLT ℝ (n + 1)).subtype
  obtain ⟨p, hp⟩ := L.range.exists_norm_sub_le_of_finiteDimensional f
  obtain ⟨q, hq⟩ := p.property
  have hqd : (q : ℝ[X]).degree ≤ n := by
    have h := mem_degreeLT.mp q.property
    by_cases hq0 : (q : ℝ[X]) = 0
    · simp [hq0]
    · rw [degree_eq_natDegree hq0] at h ⊢
      exact_mod_cast Nat.le_of_lt_succ (show (q : ℝ[X]).natDegree < n + 1 by exact_mod_cast h)
  refine ⟨q, hqd, fun r hr ↦ ?_⟩
  have hr' : r ∈ degreeLT ℝ (n + 1) := mem_degreeLT.mpr
    (hr.trans_lt (by exact_mod_cast Nat.lt_succ_self n))
  have h := hp ⟨L ⟨r, hr'⟩, LinearMap.mem_range_self L _⟩
  simpa [← hq, L, toContinuousMapOnAlgHom] using h

/-- A continuous real function has a unique best degree-`n` approximation
on a nondegenerate compact interval (ATAP, Theorem 10.1). -/
theorem existsUnique_bestApproximation {a b : ℝ} (hab : a < b)
    (n : ℕ) (f : C(Icc a b, ℝ)) :
    ∃! p : ℝ[X], p.degree ≤ n ∧ ∀ q : ℝ[X], q.degree ≤ n →
      ‖f - p.toContinuousMapOn (Icc a b)‖ ≤ ‖f - q.toContinuousMapOn (Icc a b)‖ := by
  obtain ⟨p, hp, hmin⟩ := exists_bestApproximation n f
  exact ⟨p, ⟨hp, hmin⟩, fun q hq ↦ bestApproximation_unique hab f hq.1 hp hq.2 hmin⟩

/-- Equioscillation gives an equivalent certificate for the unique minimizer. -/
theorem existsUnique_equioscillating_approximation {a b : ℝ} (hab : a < b)
    (n : ℕ) (f : C(Icc a b, ℝ)) :
    ∃! p : ℝ[X], p.degree ≤ n ∧ Equioscillates n (f - p.toContinuousMapOn (Icc a b)) := by
  obtain ⟨p, ⟨hp, hmin⟩, huniq⟩ := existsUnique_bestApproximation hab n f
  refine ⟨p, ⟨hp, equioscillates_of_bestApproximation hab f hp hmin⟩, fun q hq ↦ ?_⟩
  exact huniq q ⟨hq.1, fun r hr ↦ hq.2.norm_sub_le hq.1 hr⟩

end Polynomial
