import Init

/- This file is a review-tool fixture, never part of LeanFun's mathematical library. -/
namespace ReviewFixture
universe u
/-- A fixture docstring. -/
def region (x : Nat) : Prop := x ≤ 3
theorem witness (x : Nat) (h : region x) : region x := h
theorem identity (x : Nat) : x = x := rfl
theorem constrained (x : Nat) (h : x = 0) : x = 0 := h
def polymorphic (α : Type u) (x : α) : α := x
def argument (x : Nat) : Nat := x
structure Box where
  value : Nat
end ReviewFixture
