/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Basic

/-! # Eigenvectors of unreduced lower Hessenberg matrices
With nonzero superdiagonal entries, an eigenvector is determined by its first
component. Reference: Golub--Van Loan, Matrix Computations, eigenvalue methods.
-/

public section
namespace Matrix
variable {K : Type*} [Field K] {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) K}

/-- An eigenvector whose first component vanishes is zero for an unreduced
lower Hessenberg matrix. -/
theorem eq_zero_of_hessenberg_eigenvector
    (hband : ∀ i j : Fin (n + 1), (i : ℕ) + 1 < j → A i j = 0)
    (hsub : ∀ i : Fin n, A i.castSucc i.succ ≠ 0)
    {v : Fin (n + 1) → K} {x : K} (hv : A *ᵥ v = x • v) (hzero : v 0 = 0) : v = 0 := by
  have hall (j : ℕ) (hj : j < n + 1) : v ⟨j, hj⟩ = 0 := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases hz : j = 0
      · subst j; exact hzero
      let k : Fin n := ⟨j - 1, by omega⟩
      have hk : v k.castSucc = 0 := ih (j - 1) (by omega) (by omega)
      have he := congrFun hv k.castSucc
      change (∑ l, A k.castSucc l * v l) = x * v k.castSucc at he
      rw [hk, mul_zero, Finset.sum_eq_single k.succ] at he
      · have hvj := (mul_eq_zero.mp he).resolve_left (hsub k)
        have hjk : k.succ = (⟨j, hj⟩ : Fin (n + 1)) := by ext; dsimp [k]; omega
        rwa [hjk] at hvj
      · intro l _ hl
        by_cases hlj : (l : ℕ) < j
        · rw [ih l hlj l.isLt, mul_zero]
        · rw [hband k.castSucc l (by
            have hne : (l : ℕ) ≠ j := by
              intro h
              apply hl
              ext
              dsimp [k]
              omega
            dsimp [k]
            omega), zero_mul]
      · simp
  ext j
  exact hall j j.isLt

/-- Any eigenvector is a scalar multiple of one with nonzero first component. -/
theorem hessenberg_eigenvector_eq_smul
    (hband : ∀ i j : Fin (n + 1), (i : ℕ) + 1 < j → A i j = 0)
    (hsub : ∀ i : Fin n, A i.castSucc i.succ ≠ 0)
    {u v : Fin (n + 1) → K} {x : K} (hu : A *ᵥ u = x • u)
    (hv : A *ᵥ v = x • v) (hu0 : u 0 ≠ 0) : v = (v 0 / u 0) • u := by
  have he : A *ᵥ (v - (v 0 / u 0) • u) = x • (v - (v 0 / u 0) • u) := by
    rw [mulVec_sub, mulVec_smul, hu, hv, smul_sub, smul_comm]
  have hz : (v - (v 0 / u 0) • u) 0 = 0 := by
    simp [div_mul_cancel₀ _ hu0]
  exact sub_eq_zero.mp (eq_zero_of_hessenberg_eigenvector hband hsub he hz)

/-- Unit squared-coordinate sums fix the squared first component, independently
of the choice of eigenvector. -/
theorem hessenberg_eigenvector_first_sq_eq
    (hband : ∀ i j : Fin (n + 1), (i : ℕ) + 1 < j → A i j = 0)
    (hsub : ∀ i : Fin n, A i.castSucc i.succ ≠ 0)
    {u v : Fin (n + 1) → K} {x : K} (hu : A *ᵥ u = x • u)
    (hv : A *ᵥ v = x • v) (hu0 : u 0 ≠ 0)
    (huN : ∑ i, u i ^ 2 = 1) (hvN : ∑ i, v i ^ 2 = 1) : v 0 ^ 2 = u 0 ^ 2 := by
  have he := congrArg (fun w : Fin (n + 1) → K ↦ ∑ i, w i ^ 2)
    (hessenberg_eigenvector_eq_smul hband hsub hu hv hu0)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow] at he
  rw [← Finset.mul_sum, huN, hvN, mul_one] at he
  calc
    v 0 ^ 2 = (v 0 ^ 2 / u 0 ^ 2) * u 0 ^ 2 :=
      (div_mul_cancel₀ _ (pow_ne_zero _ hu0)).symm
    _ = u 0 ^ 2 := by rw [← div_pow, ← he, one_mul]

end Matrix
