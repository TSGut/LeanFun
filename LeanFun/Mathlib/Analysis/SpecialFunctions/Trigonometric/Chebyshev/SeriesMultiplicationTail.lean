/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.SeriesMultiplication
/-! # Classical product-coefficient tails

Absolute coefficient summability gives vanishing product tails.
Reference: Trefethen, Approximation Theory and Approximation Practice, Chapter 3.
-/

public section
open Filter
open scoped Topology
namespace Polynomial.Chebyshev

/-- Absolutely summable Chebyshev factors have a vanishing product-coefficient tail. -/
theorem tendsto_chebyshevProductCoefficients_tail {a b : ℕ → ℂ}
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖)) :
    Tendsto (fun N ↦ ∑' k, ‖chebyshevProductCoefficients
      (ChebyshevProductInput.ofSummableNorm ha hb (k + N))‖) atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun k ↦ ‖chebyshevProductCoefficients
    (ChebyshevProductInput.ofSummableNorm ha hb k)‖)

end Polynomial.Chebyshev
