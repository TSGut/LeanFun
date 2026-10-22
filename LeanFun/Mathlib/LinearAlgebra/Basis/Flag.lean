/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Basis conversion respecting an ordered filtration

Degree-compatible bases give block triangular conversion. A common scalar flag
is a stronger condition and gives scalar triangular conversion. No ordering
within a degree is inferred from the total-degree filtration.

Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

public section
namespace Module.Basis
variable {ι M R : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A conversion respecting a labelled filtration is block upper triangular. -/
theorem toMatrix_blockTriangular_of_mem_span (q p : Basis ι R M) (degree : ι → ℕ)
    (hflag : ∀ j, p j ∈ Submodule.span R (q '' {i | degree i ≤ degree j})) :
    (q.toMatrix p).BlockTriangular degree := by
  intro i j hij
  change q.repr (p j) i = 0
  by_contra h
  have hi := q.repr_support_subset_of_mem_span _ (hflag j)
    (Finsupp.mem_support_iff.mpr h)
  exact (not_le_of_gt hij) hi

/-- A shared scalar flag gives upper triangular conversion, separately from
any coarser degree filtration. -/
theorem toMatrix_isUpperTriangular_of_mem_span {n : ℕ}
    (q p : Basis (Fin n) R M)
    (hflag : ∀ j, p j ∈ Submodule.span R (q '' Set.Iic j)) :
    (q.toMatrix p).IsUpperTriangular := by
  intro i j hij
  change q.repr (p j) i = 0
  by_contra h
  have hi := q.repr_support_subset_of_mem_span _ (hflag j)
    (Finsupp.mem_support_iff.mpr h)
  exact (not_le_of_gt hij) hi

end Module.Basis
