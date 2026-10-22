/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.Product

/-! # Algebra of Laurent Toeplitz symbols modulo compact operators

Reference: Böttcher–Silbermann, Introduction to Large Truncated Toeplitz Matrices.
This is the algebraic step used for polynomial Volterra kernels in
Gutleb, Sparse spectral methods for integral equations and equilibrium measures, §2.7.
-/

@[expose] public noncomputable section
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]
local notation "H" => lp (fun _ : ℕ ↦ 𝕜) 2

/-- The constant-one symbol gives the identity operator. -/
theorem laurentToeplitz_one : laurentToeplitz (1 : LaurentPolynomial 𝕜) = 1 := by
  change laurentToeplitz (AddMonoidAlgebra.single (0 : ℤ) (1 : 𝕜)) = 1
  rw [laurentToeplitz_single, one_smul]
  rfl

/-- Compact perturbations preserve addition of Laurent Toeplitz symbols. -/
theorem isCompactOperator_add_sub_laurentToeplitz
    (A B : H →L[𝕜] H) (f g : LaurentPolynomial 𝕜)
    (hA : IsCompactOperator (A-laurentToeplitz f))
    (hB : IsCompactOperator (B-laurentToeplitz g)) :
    IsCompactOperator (A+B-laurentToeplitz (f+g)) := by
  rw [map_add, add_sub_add_comm]
  exact hA.add hB

/-- Compact perturbations preserve multiplication of Laurent Toeplitz symbols. -/
theorem isCompactOperator_mul_sub_laurentToeplitz
    (A B : H →L[𝕜] H) (f g : LaurentPolynomial 𝕜)
    (hA : IsCompactOperator (A-laurentToeplitz f))
    (hB : IsCompactOperator (B-laurentToeplitz g)) :
    IsCompactOperator (A*B-laurentToeplitz (f*g)) := by
  have he : A*B-laurentToeplitz (f*g) =
      (A-laurentToeplitz f)*B+laurentToeplitz f*(B-laurentToeplitz g)+
        (laurentToeplitz f*laurentToeplitz g-laurentToeplitz (f*g)) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [he]
  exact ((hA.comp_clm B).add (hB.clm_comp (laurentToeplitz f))).add
    (isCompactOperator_laurentToeplitz_mul_sub f g)

/-- Every nonnegative power has the corresponding power symbol modulo compact operators. -/
theorem isCompactOperator_pow_sub_laurentToeplitz
    (A : H →L[𝕜] H) (f : LaurentPolynomial 𝕜)
    (hA : IsCompactOperator (A-laurentToeplitz f)) (n : ℕ) :
    IsCompactOperator (A^n-laurentToeplitz (f^n)) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, laurentToeplitz_one, sub_self]
    exact isCompactOperator_zero
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact isCompactOperator_mul_sub_laurentToeplitz _ A _ f ih hA

end lp
