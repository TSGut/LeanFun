/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.LinearAlgebra.Matrix.InversePathCoefficient
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Separation.Basic

/-!
# Nonvanishing from a first surviving inverse coefficient

A continuous local inverse and a nonzero first power pairing give nonvanishing
throughout a sufficiently small punctured neighborhood. No analyticity or
infinite Neumann series is assumed.
Reference: finite geometric inverse expansion and continuity.
-/

public section
open Filter Topology
namespace ContinuousLinearMap
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Vanishing lower powers and a nonzero first surviving pairing force local nonvanishing. -/
theorem eventually_apply_rightInverse_ne_zero (f : R →L[ℝ] ℝ)
    (K : R) (Y : ℝ → R) (hY : ContinuousAt Y 0) (h₀ : Y 0=1)
    (hy : ∀ᶠ t in 𝓝 (0 : ℝ), (1+t • K)*Y t=1) (r : ℕ)
    (hz : ∀ q < r, f (K^q)=0) (hr : f (K^r) ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), f (Y t) ≠ 0 := by
  have hc : ContinuousAt (fun t => f (K^r*Y t)) 0 :=
    f.continuous.continuousAt.comp (continuousAt_const.mul hY)
  have hn := hc.eventually_ne (by simpa [h₀] using hr)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds,
    hy.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hi hne
  exact f.toLinearMap.apply_rightInverse_ne_zero_of_powers_vanish K (Y t) t
    (by simpa using hne) hi r hz ht

end ContinuousLinearMap
