/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.SymmetricConnectionSigns

/-! # Double symmetric Jacobi raising and strict signs
Two unit parameter raisings give three same-parity degrees with signs +,-,+.
These are the outer-factor coefficients for maximal inner-index steps in
Cartesian disk multiplication by y², in the original Jacobi normalization.
Reference: DLMF 18.9; Dunkl--Xu, Cartesian disk construction.
-/

@[expose] public section
namespace Polynomial

/-- Local classical inputs for the composed A coefficient. -/
structure JacobiSymmetricDoubleRaiseAInput (β : ℝ) (n : ℕ) : Prop where
  a : JacobiSymmetricRaiseAInput β n
  b : JacobiSymmetricRaiseAInput (β + 1) n

/-- Admissible Jacobi parameters supply all constituent coefficient domains. -/
theorem JacobiSymmetricDoubleRaiseAInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    JacobiSymmetricDoubleRaiseAInput β n :=
  ⟨JacobiSymmetricRaiseAInput.of_neg_one_lt (by linarith) _, JacobiSymmetricRaiseAInput.of_neg_one_lt (by linarith) _⟩

/-- Equal-degree coefficient after two symmetric parameter raisings. -/
noncomputable def jacobiSymmetricDoubleRaiseA (β : ℝ) (n : ℕ) (input : JacobiSymmetricDoubleRaiseAInput β n := by exact Polynomial.JacobiSymmetricDoubleRaiseAInput.of_neg_one_lt (by linarith) _) : ℝ :=
  jacobiSymmetricRaiseA β n input.a * jacobiSymmetricRaiseA (β + 1) n input.b

/-- Evaluation on the full classical coefficient domain. -/
theorem jacobiSymmetricDoubleRaiseA_apply (β : ℝ) (n : ℕ) (input : JacobiSymmetricDoubleRaiseAInput β n) :
    jacobiSymmetricDoubleRaiseA β n input =
  jacobiSymmetricRaiseA β n input.a * jacobiSymmetricRaiseA (β + 1) n input.b := rfl

/-- Local classical inputs for the composed B coefficient. -/
structure JacobiSymmetricDoubleRaiseBInput (β : ℝ) (n : ℕ) : Prop where
  a : JacobiSymmetricRaiseAInput β n
  b : JacobiSymmetricRaiseBInput (β + 1) n
  c : JacobiSymmetricRaiseBInput β n
  d : JacobiSymmetricRaiseAInput (β + 1) (n - 2)

/-- Admissible Jacobi parameters supply all constituent coefficient domains. -/
theorem JacobiSymmetricDoubleRaiseBInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    JacobiSymmetricDoubleRaiseBInput β n :=
  ⟨JacobiSymmetricRaiseAInput.of_neg_one_lt (by linarith) _, JacobiSymmetricRaiseBInput.of_neg_one_lt (by linarith) _, JacobiSymmetricRaiseBInput.of_neg_one_lt (by linarith) _, JacobiSymmetricRaiseAInput.of_neg_one_lt (by linarith) _⟩

/-- Degree-minus-two coefficient after two symmetric parameter raisings. -/
noncomputable def jacobiSymmetricDoubleRaiseB (β : ℝ) (n : ℕ) (input : JacobiSymmetricDoubleRaiseBInput β n := by exact Polynomial.JacobiSymmetricDoubleRaiseBInput.of_neg_one_lt (by linarith) _) : ℝ :=
  jacobiSymmetricRaiseA β n input.a * jacobiSymmetricRaiseB (β + 1) n input.b +
    jacobiSymmetricRaiseB β n input.c * jacobiSymmetricRaiseA (β + 1) (n - 2) input.d

/-- Evaluation on the full classical coefficient domain. -/
theorem jacobiSymmetricDoubleRaiseB_apply (β : ℝ) (n : ℕ) (input : JacobiSymmetricDoubleRaiseBInput β n) :
    jacobiSymmetricDoubleRaiseB β n input =
  jacobiSymmetricRaiseA β n input.a * jacobiSymmetricRaiseB (β + 1) n input.b +
    jacobiSymmetricRaiseB β n input.c * jacobiSymmetricRaiseA (β + 1) (n - 2) input.d := rfl

/-- Local classical inputs for the composed C coefficient. -/
structure JacobiSymmetricDoubleRaiseCInput (β : ℝ) (n : ℕ) : Prop where
  a : JacobiSymmetricRaiseBInput β n
  b : JacobiSymmetricRaiseBInput (β + 1) (n - 2)

/-- Admissible Jacobi parameters supply all constituent coefficient domains. -/
theorem JacobiSymmetricDoubleRaiseCInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    JacobiSymmetricDoubleRaiseCInput β n :=
  ⟨JacobiSymmetricRaiseBInput.of_neg_one_lt (by linarith) _, JacobiSymmetricRaiseBInput.of_neg_one_lt (by linarith) _⟩

/-- Degree-minus-four coefficient after two symmetric parameter raisings. -/
noncomputable def jacobiSymmetricDoubleRaiseC (β : ℝ) (n : ℕ) (input : JacobiSymmetricDoubleRaiseCInput β n := by exact Polynomial.JacobiSymmetricDoubleRaiseCInput.of_neg_one_lt (by linarith) _) : ℝ :=
  jacobiSymmetricRaiseB β n input.a * jacobiSymmetricRaiseB (β + 1) (n - 2) input.b

/-- Evaluation on the full classical coefficient domain. -/
theorem jacobiSymmetricDoubleRaiseC_apply (β : ℝ) (n : ℕ) (input : JacobiSymmetricDoubleRaiseCInput β n) :
    jacobiSymmetricDoubleRaiseC β n input =
  jacobiSymmetricRaiseB β n input.a * jacobiSymmetricRaiseB (β + 1) (n - 2) input.b := rfl

/-- Exact double raising, with the absent low-degree terms having zero coefficient. -/
theorem jacobi_symmetric_double_raise {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    jacobi β β n =
      jacobiSymmetricDoubleRaiseA β n • jacobi (β + 2) (β + 2) n +
      jacobiSymmetricDoubleRaiseB β n • jacobi (β + 2) (β + 2) (n - 2) +
      jacobiSymmetricDoubleRaiseC β n • jacobi (β + 2) (β + 2) (n - 4) := by
  have hb : -1 < β + 1 := by linarith
  rw [(jacobi_symmetric_raise_all hβ n).1,
    (jacobi_symmetric_raise_all hb n).1,
    (jacobi_symmetric_raise_all hb (n - 2)).1]
  simp only [jacobiSymmetricDoubleRaiseA, jacobiSymmetricDoubleRaiseB,
    jacobiSymmetricDoubleRaiseC, smul_add, add_smul, mul_smul, Nat.sub_sub,
    show β + 1 + 1 = β + 2 by ring]
  abel

/-- The highest remaining degree has a strictly positive coefficient. -/
theorem jacobiSymmetricDoubleRaiseA_pos {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    0 < jacobiSymmetricDoubleRaiseA β n :=
  mul_pos (jacobiSymmetricRaiseA_pos hβ n)
    (jacobiSymmetricRaiseA_pos (by linarith) n)

/-- The middle degree has a strictly negative coefficient whenever it exists. -/
theorem jacobiSymmetricDoubleRaiseB_neg {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    jacobiSymmetricDoubleRaiseB β (n + 2) < 0 := by
  unfold jacobiSymmetricDoubleRaiseB
  exact add_neg (mul_neg_of_pos_of_neg (jacobiSymmetricRaiseA_pos hβ _)
    (jacobiSymmetricRaiseB_neg (by linarith) n))
    (mul_neg_of_neg_of_pos (jacobiSymmetricRaiseB_neg hβ n)
      (jacobiSymmetricRaiseA_pos (by linarith) _))

/-- The lowest remaining degree has a strictly positive coefficient whenever it exists. -/
theorem jacobiSymmetricDoubleRaiseC_pos {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    0 < jacobiSymmetricDoubleRaiseC β (n + 4) := by
  unfold jacobiSymmetricDoubleRaiseC
  simp only [show n + 4 - 2 = n + 2 by omega]
  exact mul_pos_of_neg_of_neg (jacobiSymmetricRaiseB_neg hβ (n + 2))
    (jacobiSymmetricRaiseB_neg (by linarith) n)

/-- Missing middle degrees have zero coefficient. -/
theorem jacobiSymmetricDoubleRaiseB_eq_zero {β : ℝ} {n : ℕ} (hn : n < 2)
    (input : JacobiSymmetricDoubleRaiseBInput β n := by
      exact Polynomial.JacobiSymmetricDoubleRaiseBInput.of_neg_one_lt (by linarith) _) :
    jacobiSymmetricDoubleRaiseB β n input = 0 := by
  rcases n with _ | _ | n <;> (try omega) <;> simp_all [jacobiSymmetricDoubleRaiseB, jacobiSymmetricRaiseB]

/-- Missing bottom degrees have zero coefficient. -/
theorem jacobiSymmetricDoubleRaiseC_eq_zero {β : ℝ} {n : ℕ} (hn : n < 4)
    (input : JacobiSymmetricDoubleRaiseCInput β n := by
      exact Polynomial.JacobiSymmetricDoubleRaiseCInput.of_neg_one_lt (by linarith) _) :
    jacobiSymmetricDoubleRaiseC β n input = 0 := by
  rcases n with _ | _ | _ | _ | n <;> (try omega) <;>
    simp_all [jacobiSymmetricDoubleRaiseC, jacobiSymmetricRaiseB]

end Polynomial
