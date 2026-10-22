/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.ConnectionCoefficient
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.ConnectionData

/-!
# One-parameter Jacobi connection expansions

Explicit Pochhammer coefficients convert an unrestricted source first parameter
into any target in the orthogonality range. Reference: DLMF 18.18.14.
-/

public section
namespace Polynomial

/-- All displayed connection denominators are positive in the target
orthogonality range, including its exceptional-looking sum alpha+beta+1=0. -/
theorem jacobiAlphaConnectionDenominator_pos {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n k : ℕ) : 0 < jacobiAlphaConnectionDenominator α β n k := by
  unfold jacobiAlphaConnectionDenominator
  exact mul_pos (mul_pos (ascPochhammer_jacobi_leading_pos hα hβ k)
    (ascPochhammer_pos (n - k) _ (by linarith [Nat.cast_nonneg (α := ℝ) k])))
    (by positivity)

/-- The Cramer coefficient equals the explicit Pochhammer quotient (DLMF 18.18.14). -/
theorem jacobiFiniteConnectionCoefficient_eq_alpha {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (n : ℕ) (k : Fin (n + 1)) :
    jacobiFiniteConnectionCoefficient α β γ β n k ⟨(det_jacobiConnectionMatrix_pos hα hβ n).ne'⟩ =
      jacobiAlphaConnectionNumerator α β γ n k / jacobiAlphaConnectionDenominator α β n k := by
  rw [jacobiFiniteConnectionCoefficient_eq_repr hα hβ, jacobiBasis_repr_eq_coefficient hα hβ]
  have hk : (k : ℕ) + (n - k) = n := Nat.add_sub_of_le (by omega)
  have h := jacobiCoefficient_jacobi_add hα hβ γ k (n - k)
  simpa only [hk, jacobiAlphaConnectionNumerator, jacobiAlphaConnectionDenominator] using h

/-- The explicit one-parameter finite Jacobi expansion (DLMF 18.18.14). -/
theorem jacobi_eq_sum_alphaConnection {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (γ : ℝ) (n : ℕ) :
    jacobi γ β n = ∑ k : Fin (n + 1),
      (jacobiAlphaConnectionNumerator α β γ n k / jacobiAlphaConnectionDenominator α β n k) •
        jacobi α β k := by
  simpa only [jacobiFiniteConnectionCoefficient_eq_alpha hα hβ] using
    jacobi_eq_sum_finiteConnectionCoefficient_of_neg_one_lt hα hβ γ β n

/-- Clearing the common denominator gives a polynomial identity on the real
orthogonality range (DLMF 18.18.14). -/
theorem jacobiAlphaConnectionScale_smul_of_neg_one_lt {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ) (n : ℕ) :
    jacobiAlphaConnectionScale α β n • jacobi γ β n =
      ∑ k : Fin (n + 1), jacobiAlphaConnectionCleared α β γ n k • jacobi α β k := by
  rw [jacobi_eq_sum_alphaConnection hα hβ γ n, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_smul]
  congr 1
  unfold jacobiAlphaConnectionScale jacobiAlphaConnectionCleared
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j : Fin (n + 1) ↦ jacobiAlphaConnectionDenominator α β n j) (Finset.mem_univ k)]
  have hd := (jacobiAlphaConnectionDenominator_pos hα hβ n k).ne'
  field_simp

end Polynomial
