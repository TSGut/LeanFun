/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticScaling
public import LeanFun.Mathlib.Analysis.Matrix.CholeskyPath

/-! # Forced distant Cholesky entries for the even disk pencil
The concrete disk path sum forces the first-to-last entry of the trailing
Cholesky block to be nonzero in every degree, for sufficiently small parameters.
Reference: Schur complements; Gutleb--Olver--Slevinsky measure modification.
-/

@[expose] public section
open Matrix Filter
open scoped Topology
namespace MvPolynomial

/-- Half-degree r boundary indices, in increasing inner-index order. -/
def dunklXuEvenBoundary (r : ℕ) (i : Fin (r + 1)) := dunklXuEvenIndex (r - i) i

/-- Perturbation block from the top even degree to the lower degree section. -/
noncomputable def dunklXuQuadraticLeftBlock {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ) :
    Matrix (Fin (r + 1)) (DunklXuEvenInterior r) ℝ := fun i j ↦
  dunklXuQuadraticMatrix hβ u v (dunklXuEvenBoundary r i) (dunklXuEvenIndex j.1.1 j.1.2)

/-- Perturbation block from the lower degree section to the top even degree. -/
noncomputable def dunklXuQuadraticRightBlock {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ) :
    Matrix (DunklXuEvenInterior r) (Fin (r + 1)) ℝ := fun i j ↦
  dunklXuQuadraticMatrix hβ u v (dunklXuEvenIndex i.1.1 i.1.2) (dunklXuEvenBoundary r j)

/-- Perturbation within the top even degree. -/
noncomputable def dunklXuQuadraticBoundaryBlock {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := fun i j ↦
  dunklXuQuadraticMatrix hβ u v (dunklXuEvenBoundary r i) (dunklXuEvenBoundary r j)

/-- The scalar path functional is exactly the relevant matrix sandwich entry. -/
theorem dunklXuInteriorFunctional_eq_sandwich {β : ℝ} (hβ : -1 < β) (u v : ℝ) (r : ℕ)
    (M : Matrix (DunklXuEvenInterior r) (DunklXuEvenInterior r) ℝ) :
    dunklXuInteriorFunctional hβ u v r M =
      (dunklXuQuadraticLeftBlock hβ u v r * M * dunklXuQuadraticRightBlock hβ u v r) 0
        (Fin.last r) := by
  simp only [dunklXuInteriorFunctional, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
    Finset.sum_mul, dunklXuQuadraticLeftBlock, dunklXuQuadraticRightBlock,
    dunklXuEvenBoundary, Fin.val_zero, Fin.val_last, Nat.sub_zero, Nat.sub_self,
    dunklXuInteriorLeft, dunklXuInteriorRight]
  rw [Finset.sum_comm]

/-- The uneliminated first-to-last top-degree entry is zero for r>=2. -/
theorem dunklXuQuadraticBoundaryBlock_first_last {β : ℝ} (hβ : -1 < β)
    (u v : ℝ) (r : ℕ) (hr : 2 ≤ r) :
    dunklXuQuadraticBoundaryBlock hβ u v r 0 (Fin.last r) = 0 := by
  apply dunklXuQuadraticMatrix_eq_zero_of_inner_gap
  simp only [dunklXuEvenBoundary, dunklXuEvenIndex, Fin.val_zero, Fin.val_last]
  omega

/-- Every compatible triangular Gram factor has a nonzero first-to-last entry
in its top even-degree block near zero. The actual disk matrices instantiate
all path hypotheses; only the displayed factor identities remain assumptions. -/
theorem eventually_dunklXuQuadratic_cholesky_first_last_ne_zero {β : ℝ}
    (hβ : -1 < β) (u v : ℝ) (hv : v ≠ 0) (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ∀ (A : Matrix (DunklXuEvenInterior r) (DunklXuEvenInterior r) ℝ)
        (B : Matrix (DunklXuEvenInterior r) (Fin (r + 1)) ℝ)
        (D : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
        IsUnit A.det → D.IsUpperTriangular →
        A.transpose * A = 1 + t • dunklXuInteriorMatrix hβ u v r →
        A.transpose * B = t • dunklXuQuadraticRightBlock hβ u v r →
        B.transpose * A = t • dunklXuQuadraticLeftBlock hβ u v r →
        B.transpose * B + D.transpose * D = 1 + t • dunklXuQuadraticBoundaryBlock hβ u v r →
        D 0 (Fin.last r) ≠ 0 := by
  have hn := eventually_cholesky_first_row_ne_zero (dunklXuInteriorMatrix hβ u v r)
    (dunklXuQuadraticRightBlock hβ u v r) (dunklXuQuadraticLeftBlock hβ u v r)
    (Fin.last r) (r - 2)
    (fun q hq ↦ by
      rw [← dunklXuInteriorFunctional_eq_sandwich]
      exact dunklXuInterior_sandwich_eq_zero hβ u v r q (by omega))
    (by rw [← dunklXuInteriorFunctional_eq_sandwich]
        exact dunklXuInterior_first_coefficient_ne_zero_of_vertical_ne_zero hβ u v hv r hr)
  filter_upwards [hn] with t ht A B D hA hD hAA hAB hBA hDD
  apply ht A B D hA hD hAA hAB hBA
  rw [hDD, Matrix.add_apply, Matrix.smul_apply,
    dunklXuQuadraticBoundaryBlock_first_last hβ u v r hr]
  have he : (0 : Fin (r + 1)) ≠ Fin.last r := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  simp [he]

end MvPolynomial
