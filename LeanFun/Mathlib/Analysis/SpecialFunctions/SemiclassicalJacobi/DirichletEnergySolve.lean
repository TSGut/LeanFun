/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletEnergyBasis
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Convergence of the actual annular coefficient solves in energy
For every continuous load on the chosen energy completion, the finite coefficient
solutions are its Riesz solution's orthogonal projections. This proves convergence
without identifying the completion with a planar Sobolev space.
-/

@[expose] public noncomputable section
namespace Polynomial.SemiclassicalJacobiEnergy
open Matrix Filter
open scoped Topology

/-- The unique energy weak solution for a continuous load. -/
def solution (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (ℓ : Space t γ →L[ℝ] ℝ) : Space t γ :=
  (InnerProductSpace.toDual ℝ (Space t γ)).symm ℓ

/-- The energy weak equation holds against every completed test vector. -/
theorem solution_weak (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (ℓ : Space t γ →L[ℝ] ℝ)
    (z : Space t γ) : inner ℝ (solution t γ ℓ) z = ℓ z :=
  InnerProductSpace.toDual_symm_apply

/-- The energy weak solution is unique. -/
theorem existsUnique_solution (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (ℓ : Space t γ →L[ℝ] ℝ) :
    ∃! x : Space t γ, ∀ z : Space t γ, inner ℝ x z = ℓ z := by
  refine ⟨solution t γ ℓ, solution_weak t γ ℓ, ?_⟩
  intro y hy
  apply (InnerProductSpace.toDual ℝ (Space t γ)).injective
  ext z
  change inner ℝ y z = inner ℝ (solution t γ ℓ) z
  rw [hy, solution_weak]

/-- Sign convention for solving with the negative definite Laplacian matrix. -/
def load (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ) (ℓ : Space t γ →L[ℝ] ℝ) : Fin N → ℝ :=
  fun i ↦ -ℓ (basisVector t γ i)

/-- The unique solution of the already-defined finite Dirichlet matrix system. -/
def coefficients (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ)
    (ℓ : Space t γ →L[ℝ] ℝ) : Fin N → ℝ :=
  Classical.choose (existsUnique_semiclassicalJacobiDirichletSection (gt_one t) γ N (load t γ N ℓ))

/-- The chosen coefficients solve the actual square-section system. -/
theorem coefficients_spec (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ)
    (ℓ : Space t γ →L[ℝ] ℝ) :
    semiclassicalJacobiDirichletSection (gt_one t) γ N *ᵥ coefficients t γ N ℓ = load t γ N ℓ :=
  (Classical.choose_spec
    (existsUnique_semiclassicalJacobiDirichletSection (gt_one t) γ N (load t γ N ℓ))).1

/-- The actual finite coefficient solution equals the energy orthogonal projection. -/
theorem trialEmbed_coefficients_eq_projection (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ)
    (ℓ : Space t γ →L[ℝ] ℝ) :
    trialEmbed t γ N (coefficients t γ N ℓ) = projection t γ N (solution t γ ℓ) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (trialEmbed_mem t γ N _)
  intro z hz
  rw [trialSpace_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    rw [inner_sub_left, solution_weak, inner_trialEmbed_basisVector, coefficients_spec]
    simp [load]
  | zero => simp
  | add x y hx hy hx' hy' => simp [inner_add_right, hx', hy']
  | smul a x hx hx' => simp [inner_smul_right, hx']

/-- The finite coefficient solution has the best possible energy error in its trial space. -/
theorem coefficients_bestApproximation (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ)
    (ℓ : Space t γ →L[ℝ] ℝ) (y : Space t γ) (hy : y ∈ trialSpace t γ N) :
    ‖solution t γ ℓ-trialEmbed t γ N (coefficients t γ N ℓ)‖ ≤ ‖solution t γ ℓ-y‖ := by
  rw [trialEmbed_coefficients_eq_projection]
  exact projection_bestApproximation t γ N _ y hy

/-- The reconstructed solutions are uniformly stable in the energy norm. -/
theorem norm_trialEmbed_coefficients_le (t : Set.Ioi (1 : ℝ)) (γ : ℝ) (N : ℕ)
    (ℓ : Space t γ →L[ℝ] ℝ) : ‖trialEmbed t γ N (coefficients t γ N ℓ)‖ ≤ ‖ℓ‖ := by
  rw [trialEmbed_coefficients_eq_projection]
  exact ((trialSpace t γ N).norm_starProjection_apply_le (solution t γ ℓ)).trans_eq
    ((InnerProductSpace.toDual ℝ (Space t γ)).symm.norm_map ℓ)

/-- As radial degree grows, the actual finite coefficient solves converge in energy. -/
theorem tendsto_trialEmbed_coefficients (t : Set.Ioi (1 : ℝ)) (γ : ℝ)
    (ℓ : Space t γ →L[ℝ] ℝ) :
    Tendsto (fun N ↦ trialEmbed t γ N (coefficients t γ N ℓ)) atTop (𝓝 (solution t γ ℓ)) := by
  simp only [trialEmbed_coefficients_eq_projection]
  exact tendsto_projection t γ _

end Polynomial.SemiclassicalJacobiEnergy
