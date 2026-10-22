/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Compactness of finite-dimensional convex hulls
Carathéodory's theorem bounds the number of points needed in a convex combination.
This supplies compact finite certificates for uniform approximation.
-/

public section
open Set

private def convexImage {E : Type*} [AddCommGroup E] [Module ℝ E] (s : Set E) (n : ℕ) : Set E :=
  {y | ∃ (w : Fin n → ℝ) (z : Fin n → E), ((∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) ∧
    (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = y}

/-- A convex-hull point in finite dimensions has a combination with at most
`finrank + 1` terms (Carathéodory's theorem). -/
theorem mem_convexHull_exists_fin_combination {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} {y : E} (hy : y ∈ convexHull ℝ s) :
    ∃ n ≤ Module.finrank ℝ E + 1, ∃ (w : Fin n → ℝ) (z : Fin n → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = y := by
  obtain ⟨ι, hι, z, w, hz, hi, hw, hsum, heq⟩ := eq_pos_convex_span_of_mem_convexHull hy
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, hi.card_le_finrank_succ.trans ?_, w ∘ e.symm, z ∘ e.symm,
    fun i ↦ (hw _).le, ?_, fun i ↦ hz ⟨_, rfl⟩, ?_⟩
  · exact Nat.add_le_add_right (Submodule.finrank_le _) 1
  · simpa only [Function.comp_apply] using (Equiv.sum_comp e.symm w).trans hsum
  · simpa only [Function.comp_apply] using (Equiv.sum_comp e.symm (fun i ↦ w i • z i)).trans heq

/-- In a finite-dimensional real normed space, the convex hull of a compact set
is compact. This is the compact form of Carathéodory's theorem. -/
theorem IsCompact.convexHull_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  have heq : convexHull ℝ s = ⋃ n ∈ Finset.range (Module.finrank ℝ E + 2), convexImage s n := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn, w, z, hw, hsum, hz, heq⟩ := mem_convexHull_exists_fin_combination hy
      exact mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨by simp only [Finset.mem_range]; omega,
        w, z, ⟨hw, hsum⟩, hz, heq⟩⟩
    · intro hy
      obtain ⟨n, _, w, z, hw, hz, rfl⟩ := mem_iUnion.1 hy |>.imp (fun _ h ↦ mem_iUnion.1 h)
      exact (convex_convexHull ℝ s).sum_mem (fun i _ ↦ hw.1 i) hw.2
        (fun i _ ↦ subset_convexHull ℝ s (hz i))
  rw [heq]
  apply Finset.isCompact_biUnion
  intro n _
  let S : Set (Fin n → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}
  have hS : IsCompact S := by
    have h := isCompact_range (show Continuous
      (fun t : Convexity.StdSimplex ℝ (Fin n) ↦ (t.weights : Fin n → ℝ)) by fun_prop)
    rw [Convexity.StdSimplex.range_toFun_comp_weights] at h
    have heq : ((⋂ i : Fin n, {w : Fin n → ℝ | 0 ≤ w i}) ∩
        {w | ∑ i, w i = 1}) = S := by ext w; simp [S]
    exact heq ▸ h
  let K := S ×ˢ Set.pi univ (fun _ : Fin n ↦ s)
  have hK : IsCompact K := hS.prod (isCompact_univ_pi (fun _ ↦ hs))
  have him : convexImage s n = (fun wz : (Fin n → ℝ) × (Fin n → E) ↦
      ∑ i, wz.1 i • wz.2 i) '' K := by
    ext y
    simp [convexImage, K, S, Set.mem_pi, Set.mem_image, Prod.exists, and_assoc]
  rw [him]
  exact hK.image (by fun_prop)
