/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.Symbol

/-! # Algebra of continuous Toeplitz symbols modulo compact operators

Reference: Böttcher–Silbermann, Introduction to Large Truncated Toeplitz Matrices.
This is the algebraic step used for polynomial Volterra kernels in
Gutleb, Sparse spectral methods for integral equations and equilibrium measures, §2.7.
-/

@[expose] public noncomputable section
namespace AddCircle
variable {T : ℝ} [Fact (0 < T)]
local notation "H" => lp (fun _ : ℕ ↦ ℂ) 2

/-- The constant-one symbol gives the identity operator. -/
theorem continuousToeplitz_one : continuousToeplitz (1 : C(AddCircle T, ℂ)) = 1 := by
  have hf : (fourier (T := T) 0) = 1 := by ext x; exact fourier_zero
  rw [← hf, continuousToeplitz_fourier]
  rfl

/-- Compact perturbations preserve addition of continuous Toeplitz symbols. -/
theorem isCompactOperator_add_sub_continuousToeplitz
    (A B : H →L[ℂ] H) (f g : C(AddCircle T, ℂ))
    (hA : IsCompactOperator (A-continuousToeplitz f))
    (hB : IsCompactOperator (B-continuousToeplitz g)) :
    IsCompactOperator (A+B-continuousToeplitz (f+g)) := by
  rw [continuousToeplitz_add, add_sub_add_comm]
  exact hA.add hB

/-- Compact perturbations preserve multiplication of continuous Toeplitz symbols. -/
theorem isCompactOperator_mul_sub_continuousToeplitz
    (A B : H →L[ℂ] H) (f g : C(AddCircle T, ℂ))
    (hA : IsCompactOperator (A-continuousToeplitz f))
    (hB : IsCompactOperator (B-continuousToeplitz g)) :
    IsCompactOperator (A*B-continuousToeplitz (f*g)) := by
  have he : A*B-continuousToeplitz (f*g) =
      (A-continuousToeplitz f)*B+continuousToeplitz f*(B-continuousToeplitz g)+
        (continuousToeplitz f*continuousToeplitz g-continuousToeplitz (f*g)) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [he]
  exact ((hA.comp_clm B).add (hB.clm_comp (continuousToeplitz f))).add
    (isCompactOperator_continuousToeplitz_mul_sub f g)

/-- Every nonnegative power has the corresponding power symbol modulo compact operators. -/
theorem isCompactOperator_pow_sub_continuousToeplitz
    (A : H →L[ℂ] H) (f : C(AddCircle T, ℂ))
    (hA : IsCompactOperator (A-continuousToeplitz f)) (n : ℕ) :
    IsCompactOperator (A^n-continuousToeplitz (f^n)) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, continuousToeplitz_one, sub_self]
    exact isCompactOperator_zero
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact isCompactOperator_mul_sub_continuousToeplitz _ A _ f ih hA

end AddCircle
