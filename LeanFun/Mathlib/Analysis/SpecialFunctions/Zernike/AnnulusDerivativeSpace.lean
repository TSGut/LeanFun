/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusEnergySolve
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletDerivativeSpace

/-! # Concrete derivative classes for the angular annular energy space
Each normalized angular sector has a weighted L² derivative realization. Their
Hilbert sum preserves the complete energy norm and the convergence of the actual
finite coefficient solves. These are radial derivative data, not yet a Cartesian
weak gradient or a zero-trace Sobolev identification.
-/

@[expose] public noncomputable section
open Polynomial Filter
open scoped Topology
namespace MvPolynomial.AnnularEnergy

/-- Weighted L² derivative classes in all valid real angular sectors. -/
abbrev DerivativeSpace (q : Set.Ioo (0 : ℝ) 1) :=
  lp (fun s : Sector ↦ SemiclassicalJacobiEnergy.DerivativeSpace (parameter q) s.val.2) 2

/-- Realize all energy coordinates simultaneously as concrete weighted L² derivatives. -/
def derivativeRealization (q : Set.Ioo (0 : ℝ) 1) : Space q →ₗᵢ[ℝ] DerivativeSpace q where
  toFun x := ⟨fun s ↦ SemiclassicalJacobiEnergy.derivativeRealization (parameter q) s.val.2 (x s),
    memℓp_norm_iff.mp (by simpa only [LinearIsometry.norm_map] using (lp.memℓp x).norm)⟩
  map_add' x y := by
    apply lp.ext
    funext s
    exact map_add (SemiclassicalJacobiEnergy.derivativeRealization (parameter q) s.val.2) _ _
  map_smul' a x := by
    apply lp.ext
    funext s
    exact map_smul (SemiclassicalJacobiEnergy.derivativeRealization (parameter q) s.val.2) a _
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    apply tsum_congr
    intro s
    change ‖SemiclassicalJacobiEnergy.derivativeRealization (parameter q) s.val.2 (x s)‖ ^
      (2 : ENNReal).toReal = ‖x s‖ ^ (2 : ENNReal).toReal
    rw [LinearIsometry.norm_map]

/-- The realization acts sector by sector with the existing physical coordinate normalization. -/
theorem derivativeRealization_apply (q : Set.Ioo (0 : ℝ) 1) (x : Space q) (s : Sector) :
    derivativeRealization q x s =
      SemiclassicalJacobiEnergy.derivativeRealization (parameter q) s.val.2 (x s) := rfl

/-- Completed annular energy has a faithful realization in the Hilbert sum of derivative classes. -/
theorem derivativeRealization_injective (q : Set.Ioo (0 : ℝ) 1) :
    Function.Injective (derivativeRealization q) := (derivativeRealization q).injective

/-- The realized annular derivative space is closed. -/
theorem isClosed_range_derivativeRealization (q : Set.Ioo (0 : ℝ) 1) :
    IsClosed (Set.range (derivativeRealization q)) :=
  (derivativeRealization q).isometry.isClosedEmbedding.isClosed_range

/-- The finite solver's energy error equals its concrete derivative-space error. -/
theorem norm_sub_derivativeRealization_finiteSolve (q : Set.Ioo (0 : ℝ) 1)
    (c : Finset Sector × ℕ) (ℓ : Space q →L[ℝ] ℝ) :
    ‖derivativeRealization q (solution q ℓ) - derivativeRealization q (finiteSolve q c ℓ)‖ =
      ‖solution q ℓ - finiteSolve q c ℓ‖ := by
  rw [← map_sub, LinearIsometry.norm_map]

/-- Joint angular and radial convergence also holds in the concrete derivative Hilbert sum. -/
theorem tendsto_derivativeRealization_finiteSolve (q : Set.Ioo (0 : ℝ) 1)
    (ℓ : Space q →L[ℝ] ℝ) :
    Tendsto (fun N ↦ derivativeRealization q (finiteSolve q (frequencyCutoff N, N) ℓ))
      atTop (𝓝 (derivativeRealization q (solution q ℓ))) :=
  (derivativeRealization q).continuous.tendsto _ |>.comp
    (tendsto_finiteSolve_frequencyCutoff q ℓ)

end MvPolynomial.AnnularEnergy
