/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic.Abel

/-!
# Finite offset support under composition

Nested degree labels can be pairs or tuples. Composing finite conversion
sections adds their support sets; the intermediate labels must agree.
Reference: Gutleb–Olver–Slevinsky, polynomial connection operators.
-/

@[expose] public section
open scoped Pointwise
namespace Matrix
variable {ι κ τ R G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A matrix is supported on specified source-minus-target label differences. -/
def HasOffsetSupport [Zero R] (A : Matrix ι κ R) (row : ι → G) (col : κ → G)
    (S : Finset G) : Prop :=
  ∀ i j, col j-row i ∉ S → A i j = 0

/-- Compatible finite connections compose with Minkowski-sum support. The
conclusion is containment and permits further exact cancellations. -/
theorem HasOffsetSupport.mul [Semiring R] [Fintype κ]
    {A : Matrix ι κ R} {B : Matrix κ τ R}
    {row : ι → G} {mid : κ → G} {col : τ → G} {S T : Finset G}
    (hA : A.HasOffsetSupport row mid S) (hB : B.HasOffsetSupport mid col T) :
    (A * B).HasOffsetSupport row col (S+T) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases ha : mid k-row i ∈ S
  · have hb : col j-mid k ∉ T := by
      intro hb
      apply hij
      exact Finset.mem_add.mpr ⟨_, ha, _, hb, by abel⟩
    rw [hB k j hb, mul_zero]
  · rw [hA i k ha, zero_mul]

end Matrix
