/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Classical Lagrange polynomials

Denominators are nonzero in the input type. The normalized nodal product also
makes sense at an index outside the interpolation set; this domain is retained.
Reference: DLMF §3.3(i).
-/

@[expose] public section

open Polynomial
namespace Lagrange
variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- Precisely the nonzero denominators of a normalized nodal product. -/
structure BasisInput (s : Finset ι) (v : ι → F) (i : ι) : Prop where
  separated : ∀ j ∈ s.erase i, v i ≠ v j

omit [Field F] in
/-- Distinct interpolation nodes supply classical basis inputs. -/
theorem BasisInput.of_injOn {s : Finset ι} {v : ι → F}
    (hv : Set.InjOn v s) {i : ι} (hi : i ∈ s) : BasisInput s v i :=
  ⟨fun _j hj h ↦ (Finset.mem_erase.mp hj).1 (hv (Finset.mem_erase.mp hj).2 hi h.symm)⟩

omit [Field F] in
/-- For identity nodes the normalized product is valid even off the node set. -/
theorem BasisInput.id [DecidableEq F] (s : Finset F) (x : F) : BasisInput s id x := by
  classical
  exact ⟨fun _j hj h ↦ (Finset.mem_erase.mp hj).1 h.symm⟩

/-- The classical normalized nodal product (DLMF §3.3(i)). -/
noncomputable def classicalBasis (s : Finset ι) (v : ι → F) (i : ι)
    (_d : BasisInput s v i) : F[X] := Lagrange.basis s v i

/-- Product formula, with every denominator certified nonzero by the input. -/
theorem classicalBasis_eq_product (s : Finset ι) (v : ι → F) (i : ι)
    (d : BasisInput s v i) :
    classicalBasis s v i d =
      ∏ j ∈ s.erase i, Polynomial.C ((v i - v j)⁻¹) * (X - C (v j)) := rfl

/-- The normalized nodal product takes value one at its normalization point. -/
theorem eval_classicalBasis_self (s : Finset ι) (v : ι → F) (i : ι)
    (d : BasisInput s v i) : (classicalBasis s v i d).eval (v i) = 1 := by
  simp only [classicalBasis, Lagrange.basis, eval_prod]
  exact Finset.prod_eq_one fun j hj ↦ eval_basisDivisor_left_of_ne (d.separated j hj)

/-- Cardinal vanishing at every other interpolation node. -/
theorem eval_classicalBasis_of_ne {s : Finset ι} {v : ι → F} {i j : ι}
    (d : BasisInput s v i) (hij : i ≠ j) (hj : j ∈ s) :
    (classicalBasis s v i d).eval (v j) = 0 := eval_basis_of_ne hij hj

/-- A classical basis polynomial is nonzero. -/
theorem classicalBasis_ne_zero (s : Finset ι) (v : ι → F) (i : ι)
    (d : BasisInput s v i) : classicalBasis s v i d ≠ 0 := by
  intro h
  have e := eval_classicalBasis_self s v i d
  rw [h, eval_zero] at e
  exact zero_ne_one e

/-- Degree at an interpolation node (DLMF §3.3(i)). -/
theorem natDegree_classicalBasis {s : Finset ι} {v : ι → F}
    (hv : Set.InjOn v s) {i : ι} (hi : i ∈ s) :
    (classicalBasis s v i (BasisInput.of_injOn hv hi)).natDegree = s.card - 1 :=
  natDegree_basis hv hi

/-- Exact interpolation with classical basis inputs (DLMF §3.3(i)). -/
theorem eq_sum_classicalBasis {s : Finset ι} {v : ι → F}
    (hv : Set.InjOn v s) {p : F[X]} (hp : p.degree < s.card) :
    p = ∑ i : s, C (p.eval (v i)) *
      classicalBasis s v i (BasisInput.of_injOn hv i.property) := by
  classical
  calc
    p = ∑ i ∈ s, C (p.eval (v i)) * Lagrange.basis s v i := by
      simpa only [interpolate_apply] using eq_interpolate hv hp
    _ = _ := by
      exact (Finset.sum_coe_sort s (fun i ↦ C (p.eval (v i)) * Lagrange.basis s v i)).symm

end Lagrange
