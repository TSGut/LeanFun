/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletEnergyProjection

/-! # Identifying annular coefficient trial spaces in the energy completion
The trial polynomials use the existing (1,1,gamma) semiclassical basis; they are
not assumed orthonormal in the energy inner product.
-/

@[expose] public noncomputable section
namespace Polynomial.SemiclassicalJacobiEnergy
open Module Matrix

/-- The embedded semiclassical polynomial of index n. -/
def basisVector (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (n : ℕ) : Space t γ :=
  polynomialEmbed t γ (semiclassicalJacobiBasis (gt_one t)
    (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ)<1) γ n)

/-- The completed energy inner product agrees with the proved polynomial form. -/
theorem inner_polynomialEmbed (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (p q : Polynomial ℝ) :
    inner ℝ (polynomialEmbed t γ p) (polynomialEmbed t γ q) =
      -integralInner (semiclassicalJacobiMeasure t 1 1 γ) (IntegrablePair.of (semiclassicalJacobiMeasure t 1 1 γ) (semiclassicalJacobiDirichletMap ⟨t,ne_of_gt (lt_trans zero_lt_one t.property)⟩ γ p) q) := by
  simpa only [polynomialEmbed, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearIsometry.coe_toLinearMap, LinearEquiv.apply_symm_apply] using
    inner_embed t γ ((polynomialEquiv t γ).symm p) ((polynomialEquiv t γ).symm q)

/-- The first N coefficient vectors span exactly the degree-cutoff trial space. -/
theorem trialSpace_eq_span (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ) :
    trialSpace t γ N = Submodule.span ℝ (Set.range (fun i : Fin N ↦ basisVector t γ i)) := by
  let Q := semiclassicalJacobiSequence (gt_one t) (by norm_num : (-1 : ℝ)<1)
    (by norm_num : (-1 : ℝ)<1) γ
  have hs := Q.span_degreeLT (m := N) (fun i hi ↦ isUnit_iff_ne_zero.mpr
    ((semiclassicalJacobiSequence_spec (gt_one t) (by norm_num : (-1 : ℝ)<1)
      (by norm_num : (-1 : ℝ)<1) γ).2.1 i).ne')
  rw [trialSpace, ← hs, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨p, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨⟨i,hi⟩, by simp only [basisVector, semiclassicalJacobiBasis_apply, Q]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Q i, ⟨i,i.isLt,rfl⟩, by simp only [basisVector, semiclassicalJacobiBasis_apply, Q]⟩

/-- Finite coefficient synthesis in the energy completion. -/
def trialEmbed (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ) (v : Fin N → ℝ) : Space t γ :=
  polynomialEmbed t γ (semiclassicalJacobiDirichletTrial (gt_one t) γ N v)

/-- Synthesis is the finite linear combination of the existing coefficient vectors. -/
theorem trialEmbed_eq_sum (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ) (v : Fin N → ℝ) :
    trialEmbed t γ N v = ∑ i, v i • basisVector t γ i := by
  simp [trialEmbed, semiclassicalJacobiDirichletTrial, basisVector, map_sum]

/-- Finite synthesis lies in the corresponding energy trial space. -/
theorem trialEmbed_mem (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ) (v : Fin N → ℝ) :
    trialEmbed t γ N v ∈ trialSpace t γ N := by
  rw [trialSpace_eq_span, trialEmbed_eq_sum]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- The negative Dirichlet section is the energy Gram matrix of the actual trial vectors. -/
theorem inner_trialEmbed_basisVector (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ)
    (v : Fin N → ℝ) (i : Fin N) :
    inner ℝ (trialEmbed t γ N v) (basisVector t γ i) =
      -(semiclassicalJacobiDirichletSection (gt_one t) γ N *ᵥ v) i := by
  rw [trialEmbed, basisVector, inner_polynomialEmbed, semiclassicalJacobiDirichletSection_mulVec]

end Polynomial.SemiclassicalJacobiEnergy
