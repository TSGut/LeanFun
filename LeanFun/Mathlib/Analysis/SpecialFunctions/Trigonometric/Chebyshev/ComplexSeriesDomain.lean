/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexSeries

/-! # Classical complex Chebyshev series values
Reference: ATAP, Chapters 3 and 21; Olver--Townsend (2013), Sections 2--4.
-/

@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open Complex Set Filter
open scoped Topology

/-- Points where the natural-order Chebyshev partial sums have a limit. -/
abbrev ComplexChebyshevSeriesPoint (a : ℕ → ℂ) :=
  {z : ℂ // ∃ s : ℂ, Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
    a n * (T ℂ n).eval z) atTop (𝓝 s)}

/-- The classical sum, with convergence carried by the point type. -/
def complexChebyshevSeries (a : ℕ → ℂ) (z : ComplexChebyshevSeriesPoint a) : ℂ :=
  z.property.choose

/-- Natural-order partial sums converge to the classical sum. -/
theorem tendsto_complexChebyshevSeries (a : ℕ → ℂ) (z : ComplexChebyshevSeriesPoint a) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, a n * (T ℂ n).eval z.val)
      atTop (𝓝 (complexChebyshevSeries a z)) := z.property.choose_spec

/-- The classical sum is characterized by its partial-sum limit. -/
theorem complexChebyshevSeries_eq_of_tendsto {a : ℕ → ℂ}
    (z : ComplexChebyshevSeriesPoint a) {s : ℂ}
    (hs : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, a n * (T ℂ n).eval z.val)
      atTop (𝓝 s)) : complexChebyshevSeries a z = s :=
  tendsto_nhds_unique (tendsto_complexChebyshevSeries a z) hs

/-- Unconditional convergence supplies a point in the classical domain. -/
def ComplexChebyshevSeriesPoint.ofHasSum {a : ℕ → ℂ} {z s : ℂ}
    (hs : HasSum (fun n ↦ a n * (T ℂ n).eval z) s) : ComplexChebyshevSeriesPoint a :=
  ⟨z, s, hs.tendsto_sum_nat⟩

/-- Summability supplies a point in the classical domain. -/
def ComplexChebyshevSeriesPoint.ofSummable {a : ℕ → ℂ} {z : ℂ}
    (hs : Summable (fun n ↦ a n * (T ℂ n).eval z)) : ComplexChebyshevSeriesPoint a :=
  .ofHasSum hs.hasSum

/-- Internal bridge to an imported sum on its genuine convergence domain. -/
theorem complexChebyshevSeries_eq_tsum {a : ℕ → ℂ} (z : ComplexChebyshevSeriesPoint a)
    (hs : Summable (fun n ↦ a n * (T ℂ n).eval z.val)) :
    complexChebyshevSeries a z = ∑' n, a n * (T ℂ n).eval z.val :=
  complexChebyshevSeries_eq_of_tendsto z hs.hasSum.tendsto_sum_nat

/-- A supplied convergent sum is the classical value. -/
theorem complexChebyshevSeries_ofHasSum {a : ℕ → ℂ} {z s : ℂ}
    (hs : HasSum (fun n ↦ a n * (T ℂ n).eval z) s) :
    complexChebyshevSeries a (ComplexChebyshevSeriesPoint.ofHasSum hs) = s :=
  complexChebyshevSeries_eq_of_tendsto _ hs.tendsto_sum_nat

@[simp] theorem ComplexChebyshevSeriesPoint.ofHasSum_val {a : ℕ → ℂ} {z s : ℂ}
    (hs : HasSum (fun n ↦ a n * (T ℂ n).eval z) s) :
    (ComplexChebyshevSeriesPoint.ofHasSum hs).val = z := rfl

@[simp] theorem ComplexChebyshevSeriesPoint.ofSummable_val {a : ℕ → ℂ} {z : ℂ}
    (hs : Summable (fun n ↦ a n * (T ℂ n).eval z)) :
    (ComplexChebyshevSeriesPoint.ofSummable hs).val = z := rfl

end Polynomial.Chebyshev
