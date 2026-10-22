/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.BestError
public import LeanFun.Mathlib.Analysis.Normed.Module.BestApproximation
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Topology.ContinuousMap.Polynomial

/-! # Attainment of the uniform polynomial approximation error
The complex best-error infimum is attained. Real data also have a real best
approximant. Reference: ATAP, Theorem 10.1 (existence).
-/

public section
namespace Polynomial.Chebyshev
open Set

/-- Polynomial restriction as a linear map, for the existing complex convention. -/
noncomputable def polynomialOnIntervalLinear : ℂ[X] →ₗ[ℂ] C(Icc (-1 : ℝ) 1, ℂ) where
  toFun := polynomialOnInterval
  map_add' p q := by ext x; simp [polynomialOnInterval]
  map_smul' c p := by ext x; simp [polynomialOnInterval]

/-- The infimum defining the complex best uniform error is attained (ATAP 10.1). -/
theorem exists_bestUniformError (N : ℕ) (f : C(Icc (-1 : ℝ) 1, ℂ)) :
    ∃ p : ℂ[X], p.degree < ((N + 1 : ℕ) : WithBot ℕ) ∧
      ‖f - polynomialOnInterval p‖ = bestUniformError N f := by
  let L := polynomialOnIntervalLinear.comp (degreeLT ℂ (N + 1)).subtype
  obtain ⟨p, hp⟩ := L.range.exists_norm_sub_le_of_finiteDimensional f
  obtain ⟨q, hq⟩ := p.property
  refine ⟨q, mem_degreeLT.mp q.property, le_antisymm ?_ (bestUniformError_le N f (mem_degreeLT.mp q.property))⟩
  apply le_csInf
  · exact ⟨_, 0, by simp, rfl⟩
  · rintro e ⟨r, hr, rfl⟩
    have h := hp ⟨L ⟨r, mem_degreeLT.mpr hr⟩, LinearMap.mem_range_self L _⟩
    simpa [← hq, L, polynomialOnIntervalLinear, toContinuousMapOnAlgHom] using h

/-- Continuous real data have a minimizing real polynomial (ATAP 10.1). -/
theorem exists_real_bestApproximation (N : ℕ) (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    ∃ p : ℝ[X], p.degree < ((N + 1 : ℕ) : WithBot ℕ) ∧
      ∀ q : ℝ[X], q.degree < ((N + 1 : ℕ) : WithBot ℕ) →
        ‖f - p.toContinuousMapOn (Icc (-1 : ℝ) 1)‖ ≤
          ‖f - q.toContinuousMapOn (Icc (-1 : ℝ) 1)‖ := by
  let L := (toContinuousMapOnAlgHom (Icc (-1 : ℝ) 1)).toLinearMap.comp
    (degreeLT ℝ (N + 1)).subtype
  obtain ⟨p, hp⟩ := L.range.exists_norm_sub_le_of_finiteDimensional f
  obtain ⟨q, hq⟩ := p.property
  refine ⟨q, mem_degreeLT.mp q.property, fun r hr ↦ ?_⟩
  have h := hp ⟨L ⟨r, mem_degreeLT.mpr hr⟩, LinearMap.mem_range_self L _⟩
  simpa [← hq, L, polynomialOnIntervalLinear, toContinuousMapOnAlgHom] using h

end Polynomial.Chebyshev
