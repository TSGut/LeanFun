/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Matrix.InversePathCoefficient
public import LeanFun.Mathlib.LinearAlgebra.Matrix.SchurGram

/-!
# Cholesky nonvanishing from a first surviving path pairing

No continuity of the chosen factorization is required. A nonzero inverse
pairing forces the selected factor entry to be nonzero at every sufficiently
small nonzero parameter where the displayed factorization identities hold.
Reference: Gutleb–Olver–Slevinsky, measure modifications; Schur complements.
-/

@[expose] public section
open Matrix Filter Topology
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- A selected entry of rectangular left and right multiplication, as a linear functional. -/
noncomputable def sandwichEntry (F : Matrix (Fin (n+1)) ι ℝ) (E : Matrix ι (Fin (n+1)) ℝ)
    (i j : Fin (n+1)) : Matrix ι ι ℝ →ₗ[ℝ] ℝ where
  toFun M := (F*M*E) i j
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp [Matrix.mul_smul, Matrix.smul_mul]

/-- Vanishing lower powers and one surviving path pairing force local factor nonvanishing. -/
theorem eventually_cholesky_first_row_ne_zero
    (K : Matrix ι ι ℝ) (E : Matrix ι (Fin (n+1)) ℝ)
    (F : Matrix (Fin (n+1)) ι ℝ) (j : Fin (n+1)) (r : ℕ)
    (hz : ∀ q < r, (F*K^q*E) 0 j = 0) (hr : (F*K^r*E) 0 j ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ∀ (A : Matrix ι ι ℝ) (B : Matrix ι (Fin (n+1)) ℝ)
        (D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ),
        IsUnit A.det → D.IsUpperTriangular →
        A.transpose*A = 1+t • K → A.transpose*B = t • E → B.transpose*A = t • F →
        (B.transpose*B+D.transpose*D) 0 j = 0 → D 0 j ≠ 0 := by
  have hh := eventually_apply_inv_one_add_smul_ne_zero (sandwichEntry F E 0 j) K r hz hr
  filter_upwards [hh, self_mem_nhdsWithin] with t ht ht0
  intro A B D hA hD hAA hAB hBA hij
  exact schur_gram_first_row_ne_zero_of_pencil A B D K E F t (by simpa using ht0)
    hA hD hAA hAB hBA j hij ht
end Matrix
