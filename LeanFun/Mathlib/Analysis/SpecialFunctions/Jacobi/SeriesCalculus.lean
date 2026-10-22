/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.SeriesCalculus
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Derivative

/-! # Differentiating normally convergent Jacobi expansions
The shift in the coefficient formula is DLMF 18.9.15. Convergence is supplied
by the family-independent polynomial-series theorem.
-/

public section
namespace Polynomial
open Set

/-- Jacobi differentiation shifts both parameters, under an explicit summable
uniform bound on the original series. The parameters may be complex. -/
theorem hasSum_derivative_jacobi_series (α β : ℂ) {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (jacobi α β n).eval z‖ ≤ u n)
    {z : ℂ} (hz : z ∈ U) :
    HasSum (fun n ↦ a (n + 1) * ((n : ℂ) + α + β + 2) / 2 *
      (jacobi (α + 1) (β + 1) n).eval z)
      (deriv (fun w ↦ ∑' n, a n * (jacobi α β n).eval w) z) := by
  have h := hasSum_derivative_series hU hu hb hz
  have ht := (hasSum_nat_add_iff' 1).2 h
  simp only [Finset.sum_range_one, jacobi_zero, derivative_one, eval_zero, mul_zero,
    sub_zero] at ht
  convert ht using 1
  ext n
  rw [derivative_jacobi_succ]
  simp only [eval_mul, eval_C, map_div₀, map_one, map_ofNat]
  ring

end Polynomial
