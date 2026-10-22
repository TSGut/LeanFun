/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexSeries

/-!
# Real polynomial competitors from analytic functions

Taking real parts of the Chebyshev truncation gives a real polynomial of the
same degree and no larger approximation error. Reference: ATAP, Theorem 8.2.
-/

public section
namespace Polynomial.Chebyshev
open Complex Set

/-- A real polynomial competitor for the real part of an analytic function,
with the usual geometric error bound and no boundary regularity hypothesis. -/
theorem exists_real_polynomial_approximation_of_analytic {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ⟨ρ, hρ⟩))
    (hb : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖f z‖ ≤ M) (N : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ N ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖(f x).re - p.eval x‖ ≤ 2 * M / (ρ ^ N * (ρ - 1)) := by
  let c := fun n ↦ (complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun t : ℝ ↦ f t) (continuousOn_real_of_analytic hρ hf) n))
  let p : ℝ[X] := ∑ n ∈ Finset.range (N + 1), (c n).re • T ℝ n
  refine ⟨p, ?_, ?_⟩
  · apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro n hn
    apply (degree_smul_le _ _).trans
    simpa only [degree_T, Int.natAbs_natCast, Nat.cast_le] using
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  · intro x hx
    have he : (f x).re - p.eval x =
        (f x - ∑ n ∈ Finset.range (N + 1), c n * (((T ℝ n).eval x : ℝ) : ℂ)).re := by
      simp [p, eval_finsetSum, mul_re]
    rw [he, Real.norm_eq_abs]
    exact (abs_re_le_norm _).trans (norm_sub_sum_complexCoefficient_le_of_analytic hρ hf hb hx N)

end Polynomial.Chebyshev
