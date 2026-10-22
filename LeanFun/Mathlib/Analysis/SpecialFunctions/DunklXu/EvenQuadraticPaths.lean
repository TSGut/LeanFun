/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.EvenQuadratic
public import LeanFun.Mathlib.LinearAlgebra.Matrix.MaximalSandwich

/-! # Interior paths in quadratic disk elimination
The leading even-even degree section consists of a+b<r. Boundary indices are
(r,0) and (0,r), corresponding to (2r,0) and (2r,2r) in the original ordering.
Reference: finite Schur complements; Dunkl--Xu Cartesian disk construction.
-/

@[expose] public section
open Matrix
namespace MvPolynomial

/-- Even-even indices strictly below total degree 2r. -/
abbrev DunklXuEvenInterior (r : ℕ) :=
  {i : Fin r × Fin r // (i.1 : ℕ) + (i.2 : ℕ) < r}

/-- The half-inner-degree level of an interior index. -/
def dunklXuInteriorLevel {r : ℕ} (i : DunklXuEvenInterior r) : ℤ := (i.1.2 : ℕ)

/-- Restrict the normalized perturbation to the leading even-even section. -/
noncomputable def dunklXuInteriorMatrix {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ) :
    Matrix (DunklXuEvenInterior r) (DunklXuEvenInterior r) ℝ := fun i j ↦
  dunklXuQuadraticMatrix hβ u v (dunklXuEvenIndex i.1.1 i.1.2)
    (dunklXuEvenIndex j.1.1 j.1.2)

/-- The boundary row entering the leading section from (2r,0). -/
noncomputable def dunklXuInteriorLeft {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ)
    (i : DunklXuEvenInterior r) : ℝ :=
  dunklXuQuadraticMatrix hβ u v (dunklXuEvenIndex r 0) (dunklXuEvenIndex i.1.1 i.1.2)

/-- The boundary column leaving the leading section for (2r,2r). -/
noncomputable def dunklXuInteriorRight {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ)
    (i : DunklXuEvenInterior r) : ℝ :=
  dunklXuQuadraticMatrix hβ u v (dunklXuEvenIndex i.1.1 i.1.2) (dunklXuEvenIndex 0 r)

/-- Each interior multiplication step raises the inner level by at most one. -/
theorem dunklXuInteriorMatrix_level_band {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ)
    (i j : DunklXuEvenInterior r)
    (hij : dunklXuInteriorLevel i + 1 < dunklXuInteriorLevel j) :
    dunklXuInteriorMatrix hβ u v r i j = 0 := by
  apply dunklXuQuadraticMatrix_eq_zero_of_inner_gap
  simp only [dunklXuEvenIndex]
  dsimp [dunklXuInteriorLevel] at hij
  omega

/-- The entering boundary edge has the same one-level restriction. -/
theorem dunklXuInteriorLeft_level_band {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ)
    (i : DunklXuEvenInterior r) (hi : 1 < dunklXuInteriorLevel i) :
    dunklXuInteriorLeft hβ u v r i = 0 := by
  apply dunklXuQuadraticMatrix_eq_zero_of_inner_gap
  simp only [dunklXuEvenIndex]
  dsimp [dunklXuInteriorLevel] at hi
  omega

/-- The exiting boundary edge has the same one-level restriction. -/
theorem dunklXuInteriorRight_level_band {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ)
    (i : DunklXuEvenInterior r) (hi : dunklXuInteriorLevel i + 1 < r) :
    dunklXuInteriorRight hβ u v r i = 0 := by
  apply dunklXuQuadraticMatrix_eq_zero_of_inner_gap
  simp only [dunklXuEvenIndex]
  dsimp [dunklXuInteriorLevel] at hi
  omega

/-- Every elimination power before the first possible inner gap vanishes. -/
theorem dunklXuInterior_sandwich_eq_zero {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r q : ℕ)
    (hq : q + 2 < r) :
    ∑ i, ∑ j, dunklXuInteriorLeft hβ u v r i *
      (dunklXuInteriorMatrix hβ u v r ^ q) i j * dunklXuInteriorRight hβ u v r j = 0 := by
  apply sum_mul_pow_mul_eq_zero_of_level_gap _ _ _ dunklXuInteriorLevel 0 r
    (dunklXuInteriorMatrix_level_band hβ u v r)
    (dunklXuInteriorLeft_level_band hβ u v r)
    (dunklXuInteriorRight_level_band hβ u v r)
  omega

/-- The explicit path stays in degree 2r-2 between its two boundary edges. -/
def dunklXuInteriorPath (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : DunklXuEvenInterior r :=
  ⟨(⟨r - 2 - min k (r - 2), by omega⟩, ⟨min k (r - 2) + 1, by omega⟩), by dsimp; omega⟩

/-- All interior path vertices lie on the last degree layer of the leading section. -/
theorem dunklXuInteriorPath_degree (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    ((dunklXuInteriorPath r hr k).1.1 : ℕ) + (dunklXuInteriorPath r hr k).1.2 = r - 1 := by
  dsimp [dunklXuInteriorPath]
  omega

/-- Before the final interior vertex, each edge lowers the outer degree by two
and raises the inner degree by two. -/
theorem dunklXuInteriorPath_step (r : ℕ) (hr : 2 ≤ r) (k : ℕ) (hk : k < r - 2) :
    ((dunklXuInteriorPath r hr k).1.1 : ℕ) =
        ((dunklXuInteriorPath r hr (k + 1)).1.1 : ℕ) + 1 ∧
      ((dunklXuInteriorPath r hr (k + 1)).1.2 : ℕ) =
        ((dunklXuInteriorPath r hr k).1.2 : ℕ) + 1 := by
  dsimp [dunklXuInteriorPath]
  omega

end MvPolynomial
