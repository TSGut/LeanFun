/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.IteratedSeriesCalculus
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.IteratedDerivative

/-! # Higher derivatives of Jacobi series
The same normal-convergence hypothesis suffices for every derivative order.
Reference: DLMF 18.9.15, iterated; ATAP, Chapter 21.
-/

public section
namespace Polynomial
open Set

/-- Differentiating k times removes the first k modes and shifts both Jacobi
parameters by k, with the finite-product rising-factorial coefficient. -/
theorem hasSum_iterated_derivative_jacobi_series (α β : ℂ) {a : ℕ → ℂ} {u : ℕ → ℝ}
    {U : Set ℂ} (hU : IsOpen U) (hu : Summable u)
    (hb : ∀ n z, z ∈ U → ‖a n * (jacobi α β n).eval z‖ ≤ u n)
    (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    HasSum (fun n ↦ a (n + k) *
      (∏ j ∈ Finset.range k, (1 / 2 : ℂ) * ((n + k : ℂ) + α + β + j + 1)) *
        (jacobi (α + k) (β + k) n).eval z)
      (iteratedDeriv k (fun w ↦ ∑' n, a n * (jacobi α β n).eval w) z) := by
  have hs := hasSum_iterated_derivative_series (P := jacobi α β) (a := a) hU hu hb k hz
  have ht := (hasSum_nat_add_iff' k).2 hs
  have hz0 : ∑ n ∈ Finset.range k, a n * (derivative^[k] (jacobi α β n)).eval z = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [iterate_derivative_jacobi_eq_zero α β (Finset.mem_range.mp hn), eval_zero, mul_zero]
  rw [hz0, sub_zero] at ht
  simpa only [iterate_derivative_jacobi, eval_mul, eval_C, map_div₀, map_one,
    map_ofNat, mul_assoc] using ht

end Polynomial
