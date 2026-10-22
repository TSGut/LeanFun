/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletCompletion
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Convergence of annular energy projections
The finite trial spaces are the embedded radial polynomials of degree below N.
Their increasing union is dense in the energy completion. This theorem makes
no identification with a Sobolev space or assertion of a regularity rate.
-/

@[expose] public noncomputable section
namespace Polynomial.SemiclassicalJacobiEnergy
open Filter
open scoped Topology

/-- Polynomial synthesis into the energy completion, as a linear map. -/
def polynomialEmbed (t : Set.Ioi (1 : ℝ)) (γ : ℝ) : Polynomial ℝ →ₗ[ℝ] Space t γ :=
  (embed t γ).toLinearMap.comp (polynomialEquiv t γ).symm.toLinearMap

/-- The finite trial space consists of embedded polynomials of radial degree below N. -/
def trialSpace (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ) : Submodule ℝ (Space t γ) :=
  (degreeLT ℝ N).map (polynomialEmbed t γ)

instance (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ) :
    FiniteDimensional ℝ (trialSpace t γ N) := by
  let : FiniteDimensional ℝ (degreeLT ℝ N) := (degreeLTEquiv ℝ N).symm.finiteDimensional
  unfold trialSpace
  infer_instance

/-- Raising the degree cutoff nests the energy trial spaces. -/
theorem trialSpace_mono (t : Set.Ioi (1 : ℝ)) (γ : ℝ) : Monotone (trialSpace t γ) :=
  fun _ _ h ↦ Submodule.map_mono (degreeLT_mono h)

/-- Every polynomial lies in some finite trial space. -/
theorem polynomialEmbed_mem_trialSpace (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (p : Polynomial ℝ) :
    polynomialEmbed t γ p ∈ trialSpace t γ (p.natDegree+1) := by
  apply Submodule.mem_map.mpr
  refine ⟨p, ?_, rfl⟩
  rw [mem_degreeLT]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self p.natDegree)

/-- The union of finite trial spaces is dense in the chosen energy completion. -/
theorem trialSpace_closure_iSup (t : Set.Ioi (1 : ℝ)) (γ : ℝ) :
    (⨆ N, trialSpace t γ N).topologicalClosure=⊤ := by
  apply le_antisymm le_top
  intro x hx
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  apply closure_mono (s := Set.range (embed t γ)) ?_ (denseRange_embed t γ x)
  rintro y ⟨p, rfl⟩
  have hp := polynomialEmbed_mem_trialSpace t γ (polynomialEquiv t γ p)
  simp only [polynomialEmbed, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearIsometry.coe_toLinearMap] at hp
  exact (le_iSup (trialSpace t γ) _) hp

/-- Orthogonal projection in the Dirichlet energy norm. -/
def projection (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ) : Space t γ →L[ℝ] Space t γ :=
  (trialSpace t γ N).starProjection

/-- The energy projection minimizes error over the finite trial space. -/
theorem projection_bestApproximation (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ)
    (x y : Space t γ) (hy : y ∈ trialSpace t γ N) :
    ‖x-projection t γ N x‖ ≤ ‖x-y‖ := by
  rw [projection, Submodule.starProjection_minimal]
  exact ciInf_le (f := fun z : trialSpace t γ N ↦ ‖x-(z : Space t γ)‖)
    ⟨0, Set.forall_mem_range.mpr (fun _ ↦ norm_nonneg _)⟩ ⟨y,hy⟩

/-- Finite energy projections converge to every element of the energy completion. -/
theorem tendsto_projection (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (x : Space t γ) :
    Tendsto (fun N ↦ projection t γ N x) atTop (𝓝 x) :=
  Submodule.starProjection_tendsto_self (trialSpace t γ) (trialSpace_mono t γ) x
    (by rw [trialSpace_closure_iSup])

end Polynomial.SemiclassicalJacobiEnergy
