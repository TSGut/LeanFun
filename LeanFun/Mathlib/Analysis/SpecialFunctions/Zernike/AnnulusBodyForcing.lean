/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusL2
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusEnergySolve

/-! # Physical body forcing and L² convergence of annular solves
Physical L² forcing gives a continuous load on the full energy Hilbert sum.
The assembled tridiagonal coefficient solves converge to its energy solution
also in physical L². Identification with the usual Sobolev weak PDE remains
separate from this energy-completion formulation.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Filter
open scoped Topology
namespace MvPolynomial.AnnularEnergy

/-- A physical L² body force acts by pairing with the realized energy vector. -/
def bodyLoad (q : Set.Ioo (0 : ℝ) 1) (g : PhysicalL2 q) : Space q →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (PhysicalL2 q) g).comp (physicalL2 q)

/-- The full body load is exactly the physical L² pairing. -/
theorem bodyLoad_apply (q : Set.Ioo (0 : ℝ) 1) (g : PhysicalL2 q) (x : Space q) :
    bodyLoad q g x = inner ℝ g (physicalL2 q x) := rfl

/-- Physical L² forcing is bounded in the dual energy norm with constant one. -/
theorem norm_bodyLoad_le (q : Set.Ioo (0 : ℝ) 1) (g : PhysicalL2 q) :
    ‖bodyLoad q g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro x
  exact (norm_inner_le_norm g _).trans
    (mul_le_mul_of_nonneg_left (norm_physicalL2_le q x) (norm_nonneg g))

/-- Against a physical polynomial trial, the load is its ordinary area integral. -/
theorem bodyLoad_polynomialEmbed (q : Set.Ioo (0 : ℝ) 1) (g : PhysicalL2 q)
    (s : Sector) (p : Polynomial ℝ) :
    bodyLoad q g (polynomialEmbed q s p) =
      ∫ v, g v * eval v (annulusDirichletLift ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2 p)
        ∂zernikeAnnulusMeasure ⟨q,q.property.1.le,q.property.2⟩ 0 0 := by
  rw [bodyLoad_apply, physicalL2_polynomialEmbed]
  rw [← radialBodyLoad_polynomialEmbed q s g p, radialBodyLoad_apply, radialL2_polynomialEmbed]

/-- The radial load passed to the assembled solver has the inverse square-root normalization. -/
theorem sectorLoad_bodyLoad (q : Set.Ioo (0 : ℝ) 1) (g : PhysicalL2 q) (s : Sector) :
    sectorLoad q (bodyLoad q g) s =
      (Real.sqrt (annulusEnergyScale ⟨q,ne_of_lt q.property.2⟩ s.val.1 s.val.2))⁻¹ • radialBodyLoad q s g := by
  ext x
  change inner ℝ g (physicalL2 q (sectorEmbed q s x)) = _
  rw [physicalL2_sectorEmbed]
  simp [sectorL2, inner_smul_right, radialBodyLoad_apply]

/-- The full energy solution obeys the physical body-force weak equation. -/
theorem body_solution_weak (q : Set.Ioo (0 : ℝ) 1) (g : PhysicalL2 q) (z : Space q) :
    inner ℝ (solution q (bodyLoad q g)) z = inner ℝ g (physicalL2 q z) :=
  solution_weak q (bodyLoad q g) z

/-- The physical body-force problem has a unique solution in the chosen energy completion. -/
theorem existsUnique_body_solution (q : Set.Ioo (0 : ℝ) 1) (g : PhysicalL2 q) :
    ∃! x : Space q, ∀ z : Space q, inner ℝ x z = inner ℝ g (physicalL2 q z) :=
  existsUnique_solution q (bodyLoad q g)

/-- The full body-force solution is bounded by the physical L² norm of its datum. -/
theorem norm_solution_bodyLoad_le (q : Set.Ioo (0 : ℝ) 1) (g : PhysicalL2 q) :
    ‖solution q (bodyLoad q g)‖ ≤ ‖g‖ :=
  ((InnerProductSpace.toDual ℝ (Space q)).symm.norm_map _).le.trans (norm_bodyLoad_le q g)

/-- Finite body-force solutions are uniformly bounded in the full energy norm. -/
theorem norm_finiteSolve_bodyLoad_le (q : Set.Ioo (0 : ℝ) 1)
    (c : Finset Sector × ℕ) (g : PhysicalL2 q) :
    ‖finiteSolve q c (bodyLoad q g)‖ ≤ ‖g‖ :=
  (norm_finiteSolve_le q c _).trans (norm_bodyLoad_le q g)

/-- Physical L² stability is uniform in both truncation parameters. -/
theorem norm_physicalL2_finiteSolve_bodyLoad_le (q : Set.Ioo (0 : ℝ) 1)
    (c : Finset Sector × ℕ) (g : PhysicalL2 q) :
    ‖physicalL2 q (finiteSolve q c (bodyLoad q g))‖ ≤ ‖g‖ :=
  (norm_physicalL2_le q _).trans (norm_finiteSolve_bodyLoad_le q c g)

/-- The realized finite solution is precisely the sum of its computed radial reconstructions. -/
theorem physicalL2_finiteSolve (q : Set.Ioo (0 : ℝ) 1) (c : Finset Sector × ℕ)
    (ℓ : Space q →L[ℝ] ℝ) :
    physicalL2 q (finiteSolve q c ℓ) =
      ∑ s ∈ c.1, sectorL2 q s
        (SemiclassicalJacobiEnergy.trialEmbed (parameter q) s.val.2 c.2
          (SemiclassicalJacobiEnergy.coefficients (parameter q) s.val.2 c.2 (sectorLoad q ℓ s))) := by
  simp only [finiteSolve, map_sum, physicalL2_sectorEmbed]

/-- The physical L² error is bounded by the energy error. -/
theorem norm_physicalL2_error_le (q : Set.Ioo (0 : ℝ) 1) (c : Finset Sector × ℕ)
    (ℓ : Space q →L[ℝ] ℝ) :
    ‖physicalL2 q (solution q ℓ) - physicalL2 q (finiteSolve q c ℓ)‖ ≤
      ‖solution q ℓ - finiteSolve q c ℓ‖ := by
  rw [← map_sub]
  exact norm_physicalL2_le q _

/-- Energy best approximation controls the physical L² error of the actual finite solve. -/
theorem physicalL2_finiteSolve_bestApproximation (q : Set.Ioo (0 : ℝ) 1)
    (c : Finset Sector × ℕ) (ℓ : Space q →L[ℝ] ℝ) (y : Space q) (hy : y ∈ trialSpace q c) :
    ‖physicalL2 q (solution q ℓ) - physicalL2 q (finiteSolve q c ℓ)‖ ≤ ‖solution q ℓ-y‖ :=
  (norm_physicalL2_error_le q c ℓ).trans (finiteSolve_bestApproximation q c ℓ y hy)

/-- Joint angular and radial coefficient convergence holds in physical L². -/
theorem tendsto_physicalL2_finiteSolve (q : Set.Ioo (0 : ℝ) 1) (ℓ : Space q →L[ℝ] ℝ) :
    Tendsto (fun c : Finset Sector × ℕ ↦ physicalL2 q (finiteSolve q c ℓ)) atTop
      (𝓝 (physicalL2 q (solution q ℓ))) :=
  (physicalL2 q).continuous.tendsto _ |>.comp (tendsto_finiteSolve q ℓ)

/-- The common frequency and radial-degree cutoff also converges in physical L². -/
theorem tendsto_physicalL2_finiteSolve_frequencyCutoff (q : Set.Ioo (0 : ℝ) 1)
    (ℓ : Space q →L[ℝ] ℝ) :
    Tendsto (fun N ↦ physicalL2 q (finiteSolve q (frequencyCutoff N, N) ℓ)) atTop
      (𝓝 (physicalL2 q (solution q ℓ))) :=
  (tendsto_physicalL2_finiteSolve q ℓ).comp tendsto_frequencyCutoff

end MvPolynomial.AnnularEnergy
