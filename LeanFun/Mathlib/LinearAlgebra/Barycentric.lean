/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Lagrange

/-! # Classical nodal weights and barycentric interpolation
All divisions have nonzero denominators on the bundled input domains.
References: DLMF §3.3(i); ATAP Theorem 5.1.
-/
@[expose] public section
open Polynomial
namespace Lagrange
variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- Nodal product weight with its precise classical denominator domain. -/
noncomputable def classicalNodalWeight (s : Finset ι) (v : ι → F) (i : ι)
    (_d : BasisInput s v i) : F := nodalWeight s v i

/-- Classical product formula, including valid off-node extensions. -/
theorem classicalNodalWeight_apply (s : Finset ι) (v : ι → F) (i : ι)
    (d : BasisInput s v i) :
    classicalNodalWeight s v i d = ∏ j ∈ s.erase i, (v i - v j)⁻¹ := rfl

/-- A classical nodal weight cannot vanish. -/
theorem classicalNodalWeight_ne_zero (s : Finset ι) (v : ι → F) (i : ι)
    (d : BasisInput s v i) : classicalNodalWeight s v i d ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact inv_ne_zero (sub_ne_zero.mpr (d.separated j hj))

/-- At a node the weight is the reciprocal derivative of the nodal polynomial. -/
theorem classicalNodalWeight_eq_derivative {s : Finset ι} {v : ι → F} {i : ι}
    (d : BasisInput s v i) (hi : i ∈ s) :
    classicalNodalWeight s v i d = ((nodal s v).derivative.eval (v i))⁻¹ :=
  nodalWeight_eq_eval_derivative_nodal hi

/-- The derivative denominator in the classical nodal-weight formula is nonzero. -/
theorem derivative_nodal_ne_zero {s : Finset ι} {v : ι → F} {i : ι}
    (d : BasisInput s v i) (hi : i ∈ s) : (nodal s v).derivative.eval (v i) ≠ 0 := by
  rw [eval_nodal_derivative_eval_node_eq hi]
  exact eval_nodal_not_at_node d.separated
/-- First barycentric form of a classical cardinal polynomial, off its own node. -/
theorem eval_classicalBasis_not_at_node {s : Finset ι} {v : ι → F} {i : ι}
    (d : BasisInput s v i) (hi : i ∈ s) (x : {x : F // x ≠ v i}) :
    (classicalBasis s v i d).eval x.val =
      (nodal s v).eval x.val * (classicalNodalWeight s v i d * (x.val - v i)⁻¹) :=
  eval_basis_not_at_node hi x.property

/-- Distinct-node data for classical interpolation, including the empty set. -/
structure InterpolationInput (s : Finset ι) (v : ι → F) : Prop where
  distinct : Set.InjOn v s

omit [Field F] in
/-- Every interpolation node has a valid classical product. -/
theorem InterpolationInput.basis {s : Finset ι} {v : ι → F}
    (d : InterpolationInput s v) (i : s) : BasisInput s v i :=
  BasisInput.of_injOn d.distinct i.property

/-- Classical interpolation polynomial (DLMF §3.3(i)). -/
noncomputable def classicalInterpolate (s : Finset ι) (v : ι → F)
    (_d : InterpolationInput s v) (r : ι → F) : F[X] := interpolate s v r

/-- Expansion in the classical cardinal polynomials. -/
theorem classicalInterpolate_apply (s : Finset ι) (v : ι → F)
    (d : InterpolationInput s v) (r : ι → F) :
    classicalInterpolate s v d r = ∑ i : s, C (r i) * classicalBasis s v i (d.basis i) := by
  exact (Finset.sum_coe_sort s (fun i ↦ C (r i) * Lagrange.basis s v i)).symm

/-- Classical interpolation attains its data. -/
theorem eval_classicalInterpolate {s : Finset ι} {v : ι → F}
    (d : InterpolationInput s v) (r : ι → F) (i : s) :
    (classicalInterpolate s v d r).eval (v i) = r i :=
  eval_interpolate_at_node r d.distinct i.property

/-- Degree bound, including the empty interpolant. -/
theorem degree_classicalInterpolate {s : Finset ι} {v : ι → F}
    (d : InterpolationInput s v) (r : ι → F) :
    (classicalInterpolate s v d r).degree < s.card := degree_interpolate_lt r d.distinct

/-- Nonempty distinct nodes and an evaluation point off all nodes. -/
structure BarycentricInput (s : Finset ι) (v : ι → F) where
  nodes : InterpolationInput s v
  nonempty : s.Nonempty
  point : {x : F // ∀ i ∈ s, x ≠ v i}

/-- Both the nodal and point-difference denominators are nonzero. -/
theorem BarycentricInput.valid {s : Finset ι} {v : ι → F}
    (d : BarycentricInput s v) (i : s) :
    classicalNodalWeight s v i (d.nodes.basis i) ≠ 0 ∧ d.point.val - v i ≠ 0 :=
  ⟨classicalNodalWeight_ne_zero _ _ _ _, sub_ne_zero.mpr (d.point.property i i.property)⟩

/-- The barycentric denominator cannot vanish on the classical input domain. -/
theorem classicalBarycentric_denominator_ne_zero {s : Finset ι} {v : ι → F}
    (d : BarycentricInput s v) :
    (∑ i : s, classicalNodalWeight s v i (d.nodes.basis i) *
      (d.point.val - v i)⁻¹) ≠ 0 := by
  change (∑ i : s, nodalWeight s v i * (d.point.val - v i)⁻¹) ≠ 0
  rw [Finset.sum_coe_sort s (fun i ↦ nodalWeight s v i * (d.point.val - v i)⁻¹)]
  exact sum_nodalWeight_mul_inv_sub_ne_zero d.nodes.distinct d.point.property d.nonempty

/-- Second barycentric formula on its full classical domain (ATAP Theorem 5.1). -/
theorem eval_classicalInterpolate_barycentric {s : Finset ι} {v : ι → F}
    (d : BarycentricInput s v) (r : ι → F) :
    (classicalInterpolate s v d.nodes r).eval d.point.val =
      (∑ i : s, classicalNodalWeight s v i (d.nodes.basis i) *
        (d.point.val - v i)⁻¹ * r i) /
      (∑ i : s, classicalNodalWeight s v i (d.nodes.basis i) *
        (d.point.val - v i)⁻¹) := by
  change (interpolate s v r).eval d.point.val =
    (∑ i : s, nodalWeight s v i * (d.point.val - v i)⁻¹ * r i) /
    (∑ i : s, nodalWeight s v i * (d.point.val - v i)⁻¹)
  rw [Finset.sum_coe_sort s (fun i ↦ nodalWeight s v i * (d.point.val - v i)⁻¹ * r i),
    Finset.sum_coe_sort s (fun i ↦ nodalWeight s v i * (d.point.val - v i)⁻¹)]
  exact eval_interpolate_not_at_node' r d.nodes.distinct d.nonempty d.point.property

end Lagrange
