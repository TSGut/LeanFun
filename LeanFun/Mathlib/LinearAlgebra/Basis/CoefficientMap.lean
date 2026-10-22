/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Linear maps on finitely supported basis coefficients
Use the existing `Basis.toMatrix` for matrix entries, without assuming that the
bases are finite. Coefficient action is a linear map on `Finsupp`.
Reference: Olver--Townsend (2013), §2.
-/

@[expose] public section
namespace Module.Basis
variable {R M N P ι κ τ : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Express a linear map in its source and target basis coordinates
(Olver--Townsend 2013, §2). -/
noncomputable def coefficientMap (b : Basis ι R M) (c : Basis κ R N) (L : M →ₗ[R] N) :
    (ι →₀ R) →ₗ[R] (κ →₀ R) :=
  c.repr.toLinearMap.comp (L.comp b.repr.symm.toLinearMap)

/-- Coefficient action reconstructs exactly the image of a finite expansion
(Olver--Townsend 2013, §2). -/
theorem repr_symm_coefficientMap (b : Basis ι R M) (c : Basis κ R N)
    (L : M →ₗ[R] N) (v : ι →₀ R) :
    c.repr.symm (b.coefficientMap c L v) = L (b.repr.symm v) := by
  simp [coefficientMap]

/-- Columns are the target coordinates of images of source basis vectors
(Olver--Townsend 2013, §2). -/
theorem coefficientMap_single (b : Basis ι R M) (c : Basis κ R N)
    (L : M →ₗ[R] N) (j : ι) :
    b.coefficientMap c L (Finsupp.single j 1) = c.repr (L (b j)) := by
  simp [coefficientMap]

/-- Matrix entries act by a finite sum over the input support
(Olver--Townsend 2013, §2). -/
theorem coefficientMap_apply (b : Basis ι R M) (c : Basis κ R N)
    (L : M →ₗ[R] N) (v : ι →₀ R) (i : κ) :
    b.coefficientMap c L v i =
      v.sum (fun j a ↦ c.toMatrix (fun j ↦ L (b j)) i j * a) := by
  classical
  conv_lhs => rw [← v.sum_single]
  simp only [map_finsuppSum, Finsupp.sum_apply]
  simp only [coefficientMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.sum, map_smul,
    b.repr_symm_single, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, toMatrix_apply, mul_comm]

/-- Composition is exact on finitely supported coefficients, with no infinite
matrix multiplication (Olver--Townsend 2013, §2). -/
theorem coefficientMap_comp (b : Basis ι R M) (c : Basis κ R N) (d : Basis τ R P)
    (L : M →ₗ[R] N) (K : N →ₗ[R] P) :
    (c.coefficientMap d K).comp (b.coefficientMap c L) =
      b.coefficientMap d (K.comp L) := by
  ext v i
  simp [coefficientMap]

end Module.Basis
