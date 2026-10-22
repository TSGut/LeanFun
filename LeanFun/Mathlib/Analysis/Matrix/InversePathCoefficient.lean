/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Matrix.InversePathCoefficient
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# First surviving inverse coefficients for finite matrices

Finite-dimensional continuity makes a first nonzero power pairing an exact
local nonvanishing criterion for the ordinary matrix inverse.
Reference: finite geometric inverse identity; the Schur-complement method.
-/

public section
open Filter Topology
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A first nonzero power pairing survives in the inverse near the identity. -/
theorem eventually_apply_inv_one_add_smul_ne_zero
    (f : Matrix ι ι ℝ →ₗ[ℝ] ℝ) (K : Matrix ι ι ℝ) (r : ℕ)
    (hz : ∀ q < r, f (K^q) = 0) (hr : f (K^r) ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), f ((1+t • K)⁻¹) ≠ 0 := by
  have hM : Continuous (fun t : ℝ => (1 : Matrix ι ι ℝ)+t • K) := by fun_prop
  have hi : ContinuousAt (fun t : ℝ => ((1 : Matrix ι ι ℝ)+t • K)⁻¹) 0 := by
    have hh : ContinuousAt (fun M : Matrix ι ι ℝ => M⁻¹) (1 : Matrix ι ι ℝ) := by
      apply continuousAt_matrix_inv
      rw [det_one]
      have he : (Ring.inverse : ℝ → ℝ) = (fun x => x⁻¹) :=
        funext (fun x => Ring.inverse_eq_inv x)
      rw [he]
      exact continuousAt_inv₀ one_ne_zero
    have hh' : ContinuousAt (fun M : Matrix ι ι ℝ => M⁻¹)
        ((1 : Matrix ι ι ℝ)+(0 : ℝ) • K) := by simpa using hh
    apply ContinuousAt.comp (g := fun M : Matrix ι ι ℝ => M⁻¹)
      (f := fun t : ℝ => (1 : Matrix ι ι ℝ)+t • K) hh'
    exact hM.continuousAt
  have hd := hM.matrix_det.continuousAt.eventually_ne
    (by simp : ((1 : Matrix ι ι ℝ)+(0 : ℝ) • K).det ≠ 0)
  have hf : Continuous f := f.continuous_of_finiteDimensional
  have hc : ContinuousAt (fun t : ℝ => f (K^r*((1 : Matrix ι ι ℝ)+t • K)⁻¹)) 0 :=
    hf.continuousAt.comp (continuousAt_const.mul hi)
  have hn := hc.eventually_ne (by simpa using hr)
  filter_upwards [hd.filter_mono nhdsWithin_le_nhds,
    hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn ht0
  exact f.apply_rightInverse_ne_zero_of_powers_vanish K ((1+t • K)⁻¹) t
    (by simpa using ht0) (mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht)) r hz hn
end Matrix
