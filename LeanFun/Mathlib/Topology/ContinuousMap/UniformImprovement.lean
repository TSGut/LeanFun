/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.Compact

/-! # Strict improvement of a uniform approximation
A direction agreeing in sign with a nonzero error at every norm-attaining
point strictly reduces the uniform norm for a sufficiently small step.
Reference: ATAP, Theorem 10.1, perturbation argument.
-/

public section
namespace ContinuousMap
open Set

private theorem exists_positive_step {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 < t i) : ∃ u > 0, ∀ i ∈ s, u ≤ t i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨u, hu, hus⟩ := ih (fun j hj ↦ ht j (Finset.mem_insert_of_mem hj))
    refine ⟨min u (t i), lt_min hu (ht i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hus j hj)

/-- A scalar step can strictly improve an error at a single point if the error
is below the target, or the direction has the right sign at an extreme point. -/
private theorem exists_step_abs_sub_lt {e q E : ℝ} (hE : 0 < E) (he : |e| ≤ E)
    (hq : |e| = E → 0 < e * q) : ∃ t > 0, |e - t * q| < E := by
  by_cases h : |e| = E
  · have hp := hq h
    have hq0 : q ≠ 0 := by intro hq0; simp [hq0] at hp
    refine ⟨e / q, (div_pos_iff).2 (by rcases mul_pos_iff.mp hp with h | h <;> tauto), ?_⟩
    simpa [div_mul_cancel₀ _ hq0] using hE
  · have hd : 0 < E - |e| := sub_pos.mpr (lt_of_le_of_ne he h)
    let t := (E - |e|) / (2 * (|q| + 1))
    have ht : 0 < t := div_pos hd (by positivity)
    have hmul : t * (2 * (|q| + 1)) = E - |e| := by dsimp [t]; field_simp
    refine ⟨t, ht, (abs_sub _ _).trans_lt ?_⟩
    rw [abs_mul, abs_of_pos ht]
    nlinarith [abs_nonneg q]

/-- A direction with the same strict sign at every extreme point reduces the
uniform error on a compact domain (ATAP 10.1). -/
theorem exists_norm_sub_smul_lt_of_extreme_sign {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (e q : C(X, ℝ)) (he : 0 < ‖e‖)
    (hq : ∀ x, |e x| = ‖e‖ → 0 < e x * q x) :
    ∃ t : ℝ, 0 < t ∧ ‖e - t • q‖ < ‖e‖ := by
  have hpoint (x : X) : ∃ t > 0, |e x - t * q x| < ‖e‖ :=
    exists_step_abs_sub_lt he (by simpa only [Real.norm_eq_abs] using e.norm_coe_le_norm x) (hq x)
  choose t ht hbound using hpoint
  let U (x : X) : Set X := {y | |e y - t x * q y| < ‖e‖}
  have hU (x : X) : IsOpen (U x) := isOpen_lt (by fun_prop) continuous_const
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ ↦ mem_iUnion.2 ⟨x, hbound x⟩)
  obtain ⟨u, hu, hus⟩ := exists_positive_step s t (fun i _ ↦ ht i)
  refine ⟨u, hu, (norm_lt_iff _ he).2 fun y ↦ ?_⟩
  obtain ⟨x, hx, hxy⟩ := mem_iUnion.1 (hs (mem_univ y)) |>.imp (fun _ h ↦ mem_iUnion.1 h)
  have huy := hus x hx
  have hratio : 0 < u / t x := div_pos hu (ht x)
  have hratio1 : u / t x ≤ 1 := (div_le_one (ht x)).2 huy
  have hid : e y - u * q y = (1 - u / t x) * e y + (u / t x) * (e y - t x * q y) := by
    field_simp [(ht x).ne']
    ring
  change |e y - t x * q y| < ‖e‖ at hxy
  change ‖e y - u * q y‖ < ‖e‖
  rw [Real.norm_eq_abs, hid]
  calc
    _ ≤ |(1 - u / t x) * e y| + |(u / t x) * (e y - t x * q y)| := abs_add_le _ _
    _ = (1 - u / t x) * |e y| + (u / t x) * |e y - t x * q y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hratio1), abs_of_pos hratio]
    _ < (1 - u / t x) * ‖e‖ + (u / t x) * ‖e‖ :=
      add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using e.norm_coe_le_norm y)
          (sub_nonneg.mpr hratio1)) (mul_lt_mul_of_pos_left hxy hratio)
    _ = ‖e‖ := by ring

end ContinuousMap
