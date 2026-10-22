/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Product separation and rectangle identities

This is an algebraic test for a pulled-back density to be a product of two
one-variable factors. It is not a converse from sparse Cholesky factors.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, §2.6.1.
-/

@[expose] public section
namespace Function
variable {α β K : Type*} [Field K]

/-- A function of two variables is a product of functions of the individual variables. -/
def IsProductSeparated (f : α → β → K) : Prop :=
  ∃ a : α → K, ∃ b : β → K, ∀ x y, f x y = a x * b y

/-- Product separation is equivalent to all two-by-two rectangle minors vanishing. -/
theorem isProductSeparated_iff (f : α → β → K) :
    IsProductSeparated f ↔ ∀ x x' y y', f x y * f x' y' = f x y' * f x' y := by
  constructor
  · rintro ⟨a,b,h⟩ x x' y y'
    simp only [h]
    ring
  · intro h
    by_cases hz : ∀ x y, f x y = 0
    · exact ⟨fun _ => 0, fun _ => 0, by simpa using hz⟩
    · push Not at hz
      obtain ⟨x₀,y₀,h₀⟩ := hz
      refine ⟨fun x => f x y₀, fun y => f x₀ y / f x₀ y₀, ?_⟩
      intro x y
      rw [← mul_div_assoc]
      exact (eq_div_iff h₀).mpr (h x x₀ y y₀)

end Function
