/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusEnergySpace

/-! # Joint angular and radial convergence of annular coefficient solves
The finite solutions use the existing tridiagonal radial matrices in each
retained angular sector. For any continuous energy load, they converge to its
unique Riesz solution as both cutoffs grow, without a Sobolev identification.
-/

@[expose] public noncomputable section
open Polynomial Filter
open scoped Topology
namespace MvPolynomial.AnnularEnergy

/-- The completed annular energy solution of a continuous linear load. -/
def solution (q : Set.Ioo (0 : ℝ) 1) (ℓ : Space q →L[ℝ] ℝ) : Space q :=
  (InnerProductSpace.toDual ℝ (Space q)).symm ℓ

/-- The completed solution satisfies the energy equation against every test vector. -/
theorem solution_weak (q : Set.Ioo (0 : ℝ) 1) (ℓ : Space q →L[ℝ] ℝ) (z : Space q) :
    inner ℝ (solution q ℓ) z = ℓ z := InnerProductSpace.toDual_symm_apply

/-- There is exactly one completed energy solution for every continuous load. -/
theorem existsUnique_solution (q : Set.Ioo (0 : ℝ) 1) (ℓ : Space q →L[ℝ] ℝ) :
    ∃! x : Space q, ∀ z : Space q, inner ℝ x z = ℓ z := by
  refine ⟨solution q ℓ, solution_weak q ℓ, ?_⟩
  intro y hy
  apply ext_inner_right ℝ
  intro z
  rw [hy, solution_weak]

/-- Restriction of the full load to one normalized angular sector. -/
def sectorLoad (q : Set.Ioo (0 : ℝ) 1) (ℓ : Space q →L[ℝ] ℝ) (s : Sector) :
    RadialSpace q s →L[ℝ] ℝ := ℓ.comp (sectorEmbed q s)

/-- The full weak solution restricts to the existing radial weak solution in each sector. -/
theorem solution_apply (q : Set.Ioo (0 : ℝ) 1) (ℓ : Space q →L[ℝ] ℝ) (s : Sector) :
    solution q ℓ s =
      SemiclassicalJacobiEnergy.solution (parameter q) s.val.2 (sectorLoad q ℓ s) := by
  apply ext_inner_right ℝ
  intro z
  rw [SemiclassicalJacobiEnergy.solution_weak, ← lp.inner_single_right]
  exact solution_weak q ℓ (lp.single 2 s z)

/-- Reconstruct the actual finite coefficient solves in the retained angular sectors. -/
def finiteSolve (q : Set.Ioo (0 : ℝ) 1) (c : Finset Sector × ℕ)
    (ℓ : Space q →L[ℝ] ℝ) : Space q :=
  ∑ s ∈ c.1, sectorEmbed q s
    (SemiclassicalJacobiEnergy.trialEmbed (parameter q) s.val.2 c.2
      (SemiclassicalJacobiEnergy.coefficients (parameter q) s.val.2 c.2 (sectorLoad q ℓ s)))

/-- Independent tridiagonal coefficient solves are exactly the combined energy projection. -/
theorem finiteSolve_eq_projection (q : Set.Ioo (0 : ℝ) 1) (c : Finset Sector × ℕ)
    (ℓ : Space q →L[ℝ] ℝ) :
    finiteSolve q c ℓ = (trialSpace q c).starProjection (solution q ℓ) := by
  simp only [finiteSolve, SemiclassicalJacobiEnergy.trialEmbed_coefficients_eq_projection,
    ← solution_apply, sectorEmbed, lp.singleContinuousLinearMap_apply]
  exact lp.HilbertSumGalerkin.sum_projection_eq _ c (solution q ℓ)

/-- The combined finite solution is the best energy approximation in its trial space. -/
theorem finiteSolve_bestApproximation (q : Set.Ioo (0 : ℝ) 1) (c : Finset Sector × ℕ)
    (ℓ : Space q →L[ℝ] ℝ) (y : Space q) (hy : y ∈ trialSpace q c) :
    ‖solution q ℓ - finiteSolve q c ℓ‖ ≤ ‖solution q ℓ - y‖ := by
  rw [finiteSolve_eq_projection, Submodule.starProjection_minimal]
  exact ciInf_le (f := fun z : trialSpace q c ↦ ‖solution q ℓ - (z : Space q)‖)
    ⟨0, Set.forall_mem_range.mpr (fun _ ↦ norm_nonneg _)⟩ ⟨y, hy⟩

/-- Stability is uniform in both the angular and radial cutoffs. -/
theorem norm_finiteSolve_le (q : Set.Ioo (0 : ℝ) 1) (c : Finset Sector × ℕ)
    (ℓ : Space q →L[ℝ] ℝ) : ‖finiteSolve q c ℓ‖ ≤ ‖ℓ‖ := by
  rw [finiteSolve_eq_projection]
  exact ((trialSpace q c).norm_starProjection_apply_le _).trans_eq
    ((InnerProductSpace.toDual ℝ (Space q)).symm.norm_map ℓ)

/-- The finite angular/radial coefficient solves converge jointly in completed energy. -/
theorem tendsto_finiteSolve (q : Set.Ioo (0 : ℝ) 1) (ℓ : Space q →L[ℝ] ℝ) :
    Tendsto (fun c : Finset Sector × ℕ ↦ finiteSolve q c ℓ) atTop (𝓝 (solution q ℓ)) := by
  simp only [finiteSolve_eq_projection]
  apply Submodule.starProjection_tendsto_self (trialSpace q)
  · exact lp.HilbertSumGalerkin.trialSpace_mono
      (fun s : Sector ↦ SemiclassicalJacobiEnergy.trialSpace (parameter q) s.val.2)
      (fun s ↦ SemiclassicalJacobiEnergy.trialSpace_mono (parameter q) s.val.2)
  · rw [trialSpace_closure_iSup]

/-- All valid real angular harmonics of frequency strictly below N. -/
def frequencyCutoff (N : ℕ) : Finset Sector :=
  ((Finset.univ : Finset Bool).product (Finset.range N)).subtype
    (fun s ↦ s.1 = true → s.2 ≠ 0)

/-- The angular cutoff has exactly the intended frequency bound. -/
theorem mem_frequencyCutoff (N : ℕ) (s : Sector) :
    s ∈ frequencyCutoff N ↔ s.val.2 < N := by
  simp [frequencyCutoff]

/-- The usual common degree/frequency cutoff exhausts both independent cutoffs. -/
theorem tendsto_frequencyCutoff :
    Tendsto (fun N ↦ (frequencyCutoff N, N)) atTop atTop := by
  refine tendsto_atTop.2 fun c ↦ ?_
  filter_upwards [eventually_ge_atTop (max (c.1.sup fun s ↦ s.val.2 + 1) c.2)] with N hN
  constructor
  · intro s hs
    rw [mem_frequencyCutoff]
    have h := Finset.le_sup (f := fun s : Sector ↦ s.val.2 + 1) hs
    omega
  · exact (le_max_right _ _).trans hN

/-- Keeping frequencies and radial degrees below N also gives energy convergence. -/
theorem tendsto_finiteSolve_frequencyCutoff (q : Set.Ioo (0 : ℝ) 1)
    (ℓ : Space q →L[ℝ] ℝ) :
    Tendsto (fun N ↦ finiteSolve q (frequencyCutoff N, N) ℓ) atTop (𝓝 (solution q ℓ)) :=
  (tendsto_finiteSolve q ℓ).comp tendsto_frequencyCutoff

end MvPolynomial.AnnularEnergy
