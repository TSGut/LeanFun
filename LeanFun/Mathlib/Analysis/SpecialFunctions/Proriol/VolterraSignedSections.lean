/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraRawInjectivity
public import LeanFun.Mathlib.Analysis.InnerProductSpace.SignedSections
public import Mathlib.Topology.Order.IntermediateValue
@[expose] public noncomputable section
/-! # First-kind Volterra finite sections for either diagonal sign

Nonvanishing of the real polynomial diagonal suffices for invertibility and
convergent raw coefficient finite sections. No injectivity hypothesis remains.
Reference: Gutleb's thesis, §2.7; Böttcher--Silbermann, finite-section method.
-/

open Polynomial Set Filter ContinuousLinearMap
open scoped Topology
namespace MvPolynomial
/-- A nonvanishing real diagonal has one sign and a uniform positive absolute lower bound. -/
theorem exists_pos_volterra_diagonal_bound_or_neg (K : MvPolynomial (Fin 2) ℝ)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ((∀ x ∈ Icc (0 : ℝ) 1, a ≤ eval (fun _ ↦ x) K) ∨
      (∀ x ∈ Icc (0 : ℝ) 1, a ≤ -eval (fun _ ↦ x) K)) := by
  let f : ℝ → ℝ := fun x ↦ eval (fun _ ↦ x) K
  have hf : Continuous f := K.continuous_eval.comp (by fun_prop)
  have hsign : (∀ x ∈ Icc (0 : ℝ) 1, 0 < f x) ∨ (∀ x ∈ Icc (0 : ℝ) 1, f x < 0) := by
    rcases lt_or_gt_of_ne (hdiag 0 (by simp)) with hn | hp
    · right
      intro x hx
      by_contra h
      obtain ⟨y,hy,he⟩ := intermediate_value_Icc hx.1 hf.continuousOn
        (show (0 : ℝ) ∈ Icc (f 0) (f x) from ⟨hn.le,le_of_not_gt h⟩)
      exact hdiag y ⟨hy.1,hy.2.trans hx.2⟩ he
    · left
      intro x hx
      by_contra h
      obtain ⟨y,hy,he⟩ := intermediate_value_Icc' hx.1 hf.continuousOn
        (show (0 : ℝ) ∈ Icc (f x) (f 0) from ⟨le_of_not_gt h,hp.le⟩)
      exact hdiag y ⟨hy.1,hy.2.trans hx.2⟩ he
  obtain ⟨t,ht,hm⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0,by simp⟩) hf.abs.continuousOn
  refine ⟨|f t|,abs_pos.mpr (hdiag t ht),?_⟩
  rcases hsign with hp | hn
  · left; intro x hx
    have hm' : |f t| ≤ |f x| := hm hx
    rwa [abs_of_pos (hp x hx)] at hm'
  · right; intro x hx
    have hm' : |f t| ≤ |f x| := hm hx
    rwa [abs_of_neg (hn x hx)] at hm'
/-- Ordered kernel quantization respects negation. -/
theorem volterraPreconditionedL2_neg (K : MvPolynomial (Fin 2) ℝ) :
    volterraPreconditionedL2 (-K) = -volterraPreconditionedL2 K :=
  (volterraPreconditionedLinear).map_neg K
/-- A polynomial kernel with nonvanishing diagonal has an invertible raw ordered operator. -/
theorem isUnit_volterraPreconditionedL2 (K : MvPolynomial (Fin 2) ℝ)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) :
    IsUnit (volterraPreconditionedL2 K) := by
  obtain ⟨a,ha,hp|hn⟩ := exists_pos_volterra_diagonal_bound_or_neg K hdiag
  · exact isUnit_volterraPreconditionedL2_of_pos K ha hp
  · have h := isUnit_volterraPreconditionedL2_of_pos (-K) ha
      (fun x hx ↦ by simpa only [map_neg] using hn x hx)
    rw [volterraPreconditionedL2_neg] at h
    simpa only [neg_neg] using h.neg
/-- Leading raw sections are eventually invertible for either nonvanishing diagonal sign. -/
theorem eventually_isUnit_volterraPreconditionedL2_section_of_nonvanishing
    (K : MvPolynomial (Fin 2) ℝ)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) :
    ∀ᶠ N in atTop, IsUnit (coerciveFiniteSection (lp.initialL2Projection N)
      (volterraPreconditionedL2 K)) := by
  obtain ⟨a,ha,hp|hn⟩ := exists_pos_volterra_diagonal_bound_or_neg K hdiag
  · exact eventually_isUnit_volterraPreconditionedL2_section_of_pos K ha hp
  · have h := eventually_isUnit_volterraPreconditionedL2_section_of_pos (-K) ha
      (fun x hx ↦ by simpa only [map_neg] using hn x hx)
    filter_upwards [h] with N hN
    rw [volterraPreconditionedL2_neg] at hN
    exact (isUnit_coerciveFiniteSection_neg_iff _ _ (lp.initialL2Projection_idempotent N)).mp hN
/-- Leading raw coefficient solves converge for every right-hand side and either diagonal sign. -/
theorem tendsto_volterraPreconditionedL2_section_solution_of_nonvanishing
    (K : MvPolynomial (Fin 2) ℝ)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (g : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N ↦ Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
      (volterraPreconditionedL2 K)) (lp.initialL2Projection N g)) atTop
      (𝓝 (Ring.inverse (volterraPreconditionedL2 K) g)) := by
  obtain ⟨a,ha,hp|hn⟩ := exists_pos_volterra_diagonal_bound_or_neg K hdiag
  · exact tendsto_volterraPreconditionedL2_section_solution_of_pos K ha hp g
  · have h := tendsto_volterraPreconditionedL2_section_solution_of_pos (-K) ha
      (fun x hx ↦ by simpa only [map_neg] using hn x hx) (-g)
    rw [volterraPreconditionedL2_neg,
      inverse_neg_apply_neg ⟨_, isUnit_volterraPreconditionedL2 K hdiag⟩] at h
    apply h.congr'
    filter_upwards [eventually_isUnit_volterraPreconditionedL2_section_of_nonvanishing
      K hdiag] with N hN
    simpa only [map_neg] using inverse_coerciveFiniteSection_neg_apply
      (lp.initialL2Projection N) ⟨volterraPreconditionedL2 K, hN⟩
      (lp.initialL2Projection_idempotent N) g
end MvPolynomial
