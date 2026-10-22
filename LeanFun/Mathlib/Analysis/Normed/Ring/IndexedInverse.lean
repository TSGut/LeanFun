/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Group.Units.Indexed
public import Mathlib.Analysis.Normed.Ring.Units

/-! # Continuity of classical indexed inverses
Inversion is continuous near a unit of a complete normed ring, with values
restricted to the invertible indices. Reference: the Banach-algebra inverse theorem.
-/

@[expose] public section
open Filter
open scoped Topology
namespace Ring
variable {ι R : Type*} [NormedRing R] [CompleteSpace R]

omit [CompleteSpace R] in
/-- Internal bridge to imported ring inversion on the genuine domain. -/
theorem inverseAt_eq_ringInverse (A : ι → R) (i : InvertibleIndex A) :
    inverseAt A i = Ring.inverse (A i) := by
  simpa only [inverseAt, IsUnit.unit_spec] using (Ring.inverse_unit i.property.unit).symm

/-- Inverse continuity restricted to genuine inverses. -/
theorem tendsto_inverseAt {A : ι → R} {l : Filter ι} (u : Rˣ)
    (hA : Tendsto A l (𝓝 (u : R))) :
    Tendsto (inverseAt A) (invertibleIndexFilter A l) (𝓝 (↑(u⁻¹) : R)) := by
  have h := (NormedRing.inverse_continuousAt u).tendsto.comp hA
  have hh := h.comp (Filter.tendsto_comap :
    Tendsto (Subtype.val : InvertibleIndex A → ι) (Filter.comap Subtype.val l) l)
  change Tendsto (fun i ↦ inverseAt A i) (Filter.comap Subtype.val l) _
  simpa only [Function.comp_def, inverseAt_eq_ringInverse, Ring.inverse_unit] using hh
end Ring
