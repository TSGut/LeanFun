/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
/-! # Classical real suprema
Nonempty bounded sets have genuine least upper bounds.
-/
@[expose] public section
namespace Real
/-- The classical domain of a finite real supremum. -/
structure SupremumInput where
  carrier : Set ℝ
  nonempty : carrier.Nonempty
  bounded : BddAbove carrier
/-- Supremum of a nonempty bounded real set. -/
noncomputable def classicalSup (d : SupremumInput) : ℝ := sSup d.carrier
/-- The classical supremum is the least upper bound. -/
theorem classicalSup_isLUB (d : SupremumInput) : IsLUB d.carrier (classicalSup d) :=
  isLUB_csSup d.nonempty d.bounded
end Real
