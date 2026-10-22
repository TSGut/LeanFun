/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Ring.GeometricInverse
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Basic.Real.Basic

/-!
# First surviving coefficient of a finite inverse pairing

A linear functional may be a matrix entry or a row-column pairing. Vanishing
lower powers leaves an exact factorization, with an inverse-dependent remainder.
Unlike an infinite Neumann expansion this identity needs no convergence bound.
Reference: finite geometric sums and the Schur-complement elimination formula.
-/

public section
namespace LinearMap
variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- Exact factorization after all lower inverse-path coefficients vanish. -/
theorem apply_rightInverse_eq_of_powers_vanish (f : R →ₗ[ℝ] ℝ)
    (K Y : R) (t : ℝ) (hy : (1+t • K)*Y=1) (r : ℕ)
    (hz : ∀ q < r, f (K^q)=0) :
    f Y = (-t)^r * f (K^r*Y) := by
  have he := eq_geom_sum_add_pow_mul_of_one_sub_mul_eq_one (-t • K) Y
    (by simpa using hy) r
  conv_lhs => rw [he, map_add, map_sum]
  have hs : (∑ q ∈ Finset.range r, f ((-t • K)^q))=0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rw [smul_pow, map_smul, hz q (Finset.mem_range.mp hq), smul_zero]
  rw [hs, zero_add, smul_pow, smul_mul_assoc, map_smul, smul_eq_mul]

/-- A nonzero surviving inverse-path remainder gives a nonzero pairing. -/
theorem apply_rightInverse_ne_zero_of_powers_vanish (f : R →ₗ[ℝ] ℝ)
    (K Y : R) (t : ℝ) (ht : t ≠ 0) (hy : (1+t • K)*Y=1) (r : ℕ)
    (hz : ∀ q < r, f (K^q)=0) (hr : f (K^r*Y) ≠ 0) : f Y ≠ 0 := by
  rw [f.apply_rightInverse_eq_of_powers_vanish K Y t hy r hz]
  exact mul_ne_zero (pow_ne_zero r (neg_ne_zero.mpr ht)) hr

end LinearMap
