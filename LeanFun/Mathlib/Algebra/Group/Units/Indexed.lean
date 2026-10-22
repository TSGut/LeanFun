/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Classical inversion along an indexed family
The invertible indices carry actual two-sided inverses. Restriction of a filter
to an eventually invertible family preserves its limiting process.
Reference: inversion in the group of units and restriction of filters.
-/

@[expose] public section
open Filter
namespace Ring
variable {ι R : Type*} [Monoid R]

/-- Indices at which a family has a two-sided inverse. -/
abbrev InvertibleIndex (A : ι → R) := {i : ι // IsUnit (A i)}

/-- Inversion along a family, defined only at its invertible indices. -/
noncomputable def inverseAt (A : ι → R) (i : InvertibleIndex A) : R :=
  ↑(i.property.unit⁻¹)

/-- The inverse has the two defining identities. -/
theorem inverseAt_mul (A : ι → R) (i : InvertibleIndex A) :
    inverseAt A i * A i = 1 ∧ A i * inverseAt A i = 1 := by
  exact ⟨by simpa only [inverseAt, IsUnit.unit_spec] using Units.inv_mul i.property.unit,
    by simpa only [inverseAt, IsUnit.unit_spec] using Units.mul_inv i.property.unit⟩

/-- Restrict a limiting process to the indices where inversion exists. -/
def invertibleIndexFilter (A : ι → R) (l : Filter ι) : Filter (InvertibleIndex A) :=
  Filter.comap Subtype.val l

/-- Eventual invertibility preserves the original limiting filter exactly. -/
theorem map_invertibleIndexFilter (A : ι → R) (l : Filter ι)
    (hA : ∀ᶠ i in l, IsUnit (A i)) :
    Filter.map Subtype.val (invertibleIndexFilter A l) = l := by
  apply Filter.map_comap_of_mem
  exact hA.mono (fun i hi ↦ ⟨⟨i, hi⟩, rfl⟩)

/-- Restriction to an eventually invertible family is nonvacuous. -/
theorem invertibleIndexFilter_neBot (A : ι → R) (l : Filter ι) [NeBot l]
    (hA : ∀ᶠ i in l, IsUnit (A i)) : NeBot (invertibleIndexFilter A l) := by
  apply Filter.NeBot.comap_of_range_mem ‹NeBot l›
  exact hA.mono (fun i hi ↦ ⟨⟨i, hi⟩, rfl⟩)
end Ring
