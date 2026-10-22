/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletGalerkin

/-! # Energy best approximation for polynomial annular Galerkin solutions
The result is algebraic and requires a polynomial exact solution. Extending to
weak solutions requires a completed energy space and its analytic interpretation.
Reference: the Galerkin orthogonality and Pythagorean energy argument.
-/

@[expose] public section
open Matrix
namespace Polynomial

/-- Squared Dirichlet energy in one radial sector. -/
noncomputable def semiclassicalJacobiDirichletEnergy (t : Set.Ioi (1 : ℝ)) (γ : ℝ)
    (p : ℝ[X]) : ℝ :=
  -integralInner (semiclassicalJacobiMeasure t 1 1 γ)
    (IntegrablePair.of (semiclassicalJacobiMeasure t 1 1 γ)
      (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ p) p
      (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one
        (γ := γ) t.property).integrable_mul _ _))

/-- Dirichlet energy is nonnegative. -/
theorem semiclassicalJacobiDirichletEnergy_nonneg {t : ℝ} (ht : 1<t) (γ : ℝ) (p : ℝ[X]) :
    0 ≤ semiclassicalJacobiDirichletEnergy ⟨t, ht⟩ γ p := by
  by_cases hp : p=0
  · simp [hp, semiclassicalJacobiDirichletEnergy]
  · exact (neg_pos.mpr (integralInner_semiclassicalJacobi_dirichlet_neg ht γ hp)).le

/-- Energy orthogonality gives the exact Pythagorean error identity. -/
theorem semiclassicalJacobiDirichletEnergy_pythagoras {t : ℝ} (ht : 1<t) (γ : ℝ)
    (p q : ℝ[X])
    (h : integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ p) q (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) ht).integrable_mul _ _))=0) :
    semiclassicalJacobiDirichletEnergy ⟨t, ht⟩ γ (p+q) =
      semiclassicalJacobiDirichletEnergy ⟨t, ht⟩ γ p+semiclassicalJacobiDirichletEnergy ⟨t, ht⟩ γ q := by
  have hμ := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) ht
    (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ)<1)
  have hr (u v w : ℝ[X]) : integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) u (v+w) (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) ht).integrable_mul _ _)) =
      integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) u v (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) ht).integrable_mul _ _))+
        integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) u w (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) ht).integrable_mul _ _)) := by
    rw [integralInner_comm, integralInner_add_left hμ]
    rw [integralInner_comm _ v u, integralInner_comm _ w u]
  unfold semiclassicalJacobiDirichletEnergy
  simp only [map_add]
  rw [integralInner_add_left hμ, hr, hr,
    integralInner_semiclassicalJacobi_dirichlet_symm ht γ q p, h]
  ring

/-- Galerkin orthogonality makes the discrete polynomial solution energy-optimal. -/
theorem semiclassicalJacobiDirichletGalerkin_bestApproximation {t : ℝ} (ht : 1<t)
    (γ : ℝ) (N : ℕ) (u : ℝ[X]) (v : Fin N → ℝ)
    (hv : semiclassicalJacobiDirichletSection ht γ N *ᵥ v =
      semiclassicalJacobiDirichletLoad ht γ N (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ u))
    (w : Fin N → ℝ) :
    semiclassicalJacobiDirichletEnergy ⟨t, ht⟩ γ (u-semiclassicalJacobiDirichletTrial ht γ N v) ≤
      semiclassicalJacobiDirichletEnergy ⟨t, ht⟩ γ (u-semiclassicalJacobiDirichletTrial ht γ N w) := by
  let vP := semiclassicalJacobiDirichletTrial ht γ N v
  let wP := semiclassicalJacobiDirichletTrial ht γ N w
  have h := (semiclassicalJacobiDirichletSection_eq_iff_galerkin ht γ N _ v).mp hv (v-w)
  have he : semiclassicalJacobiDirichletTrial ht γ N (v-w)=vP-wP := by
    simp [semiclassicalJacobiDirichletTrial, vP, wP, sub_smul, Finset.sum_sub_distrib]
  simp only [he, ← map_sub] at h
  have ho : integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ (u-vP)) (vP-wP) (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) ht).integrable_mul _ _))=0 := by
    have hm : u-vP=-(vP-u) := by abel
    simp only [hm, map_neg, ← neg_one_smul ℝ
      (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one ht)⟩ γ (vP-u))]
    rw [integralInner_smul_left (h := (hasFiniteMoments_semiclassicalJacobiMeasure_one_one (γ := γ) ht).integrable_mul _ _), h, mul_zero]
  have hp := semiclassicalJacobiDirichletEnergy_pythagoras ht γ (u-vP) (vP-wP) ho
  have hsum : (u-vP)+(vP-wP)=u-wP := by abel
  simp only [hsum] at hp
  have hn := semiclassicalJacobiDirichletEnergy_nonneg ht γ (vP-wP)
  change semiclassicalJacobiDirichletEnergy ⟨t, ht⟩ γ (u-vP) ≤
    semiclassicalJacobiDirichletEnergy ⟨t, ht⟩ γ (u-wP)
  linarith

end Polynomial
