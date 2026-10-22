/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.MvPolynomial.DunklXu
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.SymmetricConnectionSigns
import Mathlib.Tactic.Ring

/-!
# Four-term Cartesian disk parameter raising

The two symmetric Jacobi connections give the four allowed disk indices.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, disk families.
-/

@[expose] public section
open Polynomial
namespace MvPolynomial

/-- Constituent coefficient domains for the Cartesian A entry. -/
structure DunklXuDiskRaiseAInput (β : ℝ) (n k : ℕ) : Prop where
  inner : JacobiSymmetricRaiseAInput β k
  outer : JacobiSymmetricRaiseAInput (β + k + 1 / 2) (n-k)

/-- The full disk orthogonality range supplies the local coefficient inputs. -/
theorem DunklXuDiskRaiseAInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    DunklXuDiskRaiseAInput β n k := by
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hk2 := Nat.cast_nonneg (α := ℝ) (k-2)
  refine ⟨JacobiSymmetricRaiseAInput.of_neg_one_lt hβ _, ?_⟩
  exact JacobiSymmetricRaiseAInput.of_neg_one_lt (by linarith) _

/-- Coefficient at `(n,k)` in the Cartesian disk parameter-raising formula. -/
noncomputable def dunklXuDiskRaiseA (β : ℝ) (n k : ℕ) (input : DunklXuDiskRaiseAInput β n k := by exact MvPolynomial.DunklXuDiskRaiseAInput.of_neg_one_lt (by linarith) _ _) : ℝ :=
  jacobiSymmetricRaiseA β k input.inner * jacobiSymmetricRaiseA (β + k + 1 / 2) (n - k) input.outer

/-- Evaluation on the full classical coefficient domain. -/
theorem dunklXuDiskRaiseA_apply (β : ℝ) (n k : ℕ) (input : DunklXuDiskRaiseAInput β n k) :
    dunklXuDiskRaiseA β n k input =
  jacobiSymmetricRaiseA β k input.inner * jacobiSymmetricRaiseA (β + k + 1 / 2) (n - k) input.outer := rfl

/-- Constituent coefficient domains for the Cartesian B entry. -/
structure DunklXuDiskRaiseBInput (β : ℝ) (n k : ℕ) : Prop where
  inner : JacobiSymmetricRaiseAInput β k
  outer : JacobiSymmetricRaiseBInput (β + k + 1 / 2) (n-k)

/-- The full disk orthogonality range supplies the local coefficient inputs. -/
theorem DunklXuDiskRaiseBInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    DunklXuDiskRaiseBInput β n k := by
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hk2 := Nat.cast_nonneg (α := ℝ) (k-2)
  refine ⟨JacobiSymmetricRaiseAInput.of_neg_one_lt hβ _, ?_⟩
  exact JacobiSymmetricRaiseBInput.of_neg_one_lt (by linarith) _

/-- Coefficient at `(n-2,k)`; it vanishes when the outer degree is below two. -/
noncomputable def dunklXuDiskRaiseB (β : ℝ) (n k : ℕ) (input : DunklXuDiskRaiseBInput β n k := by exact MvPolynomial.DunklXuDiskRaiseBInput.of_neg_one_lt (by linarith) _ _) : ℝ :=
  jacobiSymmetricRaiseA β k input.inner * jacobiSymmetricRaiseB (β + k + 1 / 2) (n - k) input.outer

/-- Evaluation on the full classical coefficient domain. -/
theorem dunklXuDiskRaiseB_apply (β : ℝ) (n k : ℕ) (input : DunklXuDiskRaiseBInput β n k) :
    dunklXuDiskRaiseB β n k input =
  jacobiSymmetricRaiseA β k input.inner * jacobiSymmetricRaiseB (β + k + 1 / 2) (n - k) input.outer := rfl

/-- Constituent coefficient domains for the Cartesian C entry. -/
structure DunklXuDiskRaiseCInput (β : ℝ) (n k : ℕ) : Prop where
  inner : JacobiSymmetricRaiseBInput β k
  outer : 2 ≤ k → JacobiSymmetricLowerInput (β + 1 + (k - 2 : ℕ) + 1 / 2) (n-k)

/-- The full disk orthogonality range supplies the local coefficient inputs. -/
theorem DunklXuDiskRaiseCInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    DunklXuDiskRaiseCInput β n k := by
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hk2 := Nat.cast_nonneg (α := ℝ) (k-2)
  refine ⟨JacobiSymmetricRaiseBInput.of_neg_one_lt hβ _, ?_⟩
  intro _
  exact JacobiSymmetricLowerInput.of_neg_one_lt (by linarith) _

/-- Coefficient at `(n,k-2)`, with the absent inner degrees set to zero. -/
noncomputable def dunklXuDiskRaiseC (β : ℝ) (n k : ℕ) (input : DunklXuDiskRaiseCInput β n k := by exact MvPolynomial.DunklXuDiskRaiseCInput.of_neg_one_lt (by linarith) _ _) : ℝ :=
  if hk : k < 2 then 0 else
    jacobiSymmetricRaiseB β k input.inner * jacobiSymmetricLowerA (β + 1 + (k - 2 : ℕ) + 1 / 2) (n - k) (input.outer (Nat.le_of_not_lt hk))

/-- Evaluation on the full classical coefficient domain. -/
theorem dunklXuDiskRaiseC_apply (β : ℝ) (n k : ℕ) (input : DunklXuDiskRaiseCInput β n k) :
    dunklXuDiskRaiseC β n k input =
  if hk : k < 2 then 0 else
    jacobiSymmetricRaiseB β k input.inner * jacobiSymmetricLowerA (β + 1 + (k - 2 : ℕ) + 1 / 2) (n - k) (input.outer (Nat.le_of_not_lt hk)) := rfl

/-- Constituent coefficient domains for the Cartesian D entry. -/
structure DunklXuDiskRaiseDInput (β : ℝ) (n k : ℕ) : Prop where
  inner : JacobiSymmetricRaiseBInput β k
  outer : 2 ≤ k → JacobiSymmetricLowerInput (β + 1 + (k - 2 : ℕ) + 1 / 2) (n-k)

/-- The full disk orthogonality range supplies the local coefficient inputs. -/
theorem DunklXuDiskRaiseDInput.of_neg_one_lt {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    DunklXuDiskRaiseDInput β n k := by
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hk2 := Nat.cast_nonneg (α := ℝ) (k-2)
  refine ⟨JacobiSymmetricRaiseBInput.of_neg_one_lt hβ _, ?_⟩
  intro _
  exact JacobiSymmetricLowerInput.of_neg_one_lt (by linarith) _

/-- Coefficient at `(n-2,k-2)`, with the absent inner degrees set to zero. -/
noncomputable def dunklXuDiskRaiseD (β : ℝ) (n k : ℕ) (input : DunklXuDiskRaiseDInput β n k := by exact MvPolynomial.DunklXuDiskRaiseDInput.of_neg_one_lt (by linarith) _ _) : ℝ :=
  if hk : k < 2 then 0 else
    jacobiSymmetricRaiseB β k input.inner * jacobiSymmetricLowerB (β + 1 + (k - 2 : ℕ) + 1 / 2) (n - k) (input.outer (Nat.le_of_not_lt hk))

/-- Evaluation on the full classical coefficient domain. -/
theorem dunklXuDiskRaiseD_apply (β : ℝ) (n k : ℕ) (input : DunklXuDiskRaiseDInput β n k) :
    dunklXuDiskRaiseD β n k input =
  if hk : k < 2 then 0 else
    jacobiSymmetricRaiseB β k input.inner * jacobiSymmetricLowerB (β + 1 + (k - 2 : ℕ) + 1 / 2) (n - k) (input.outer (Nat.le_of_not_lt hk)) := rfl

/-- Raising the disk parameter has four-term support. Coefficients at indices
which would have negative degree or invalid inner index vanish explicitly. -/
theorem dunklXuDisk_raise {β : ℝ} (hβ : -1 < β) (n k : ℕ) (hk : k ≤ n) :
    0 < dunklXuDiskRaiseA β n k ∧ dunklXuDisk β n k =
      dunklXuDiskRaiseA β n k • dunklXuDisk (β + 1) n k +
      dunklXuDiskRaiseB β n k • dunklXuDisk (β + 1) (n - 2) k +
      dunklXuDiskRaiseC β n k • dunklXuDisk (β + 1) n (k - 2) +
      dunklXuDiskRaiseD β n k • dunklXuDisk (β + 1) (n - 2) (k - 2) ∧
      (n < k + 2 → dunklXuDiskRaiseB β n k = 0) ∧
      (k < 2 → dunklXuDiskRaiseC β n k = 0 ∧ dunklXuDiskRaiseD β n k = 0) := by
  have ha : -1 < β + k + 1 / 2 := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  let a := jacobiSymmetricRaiseA β k
  let b := jacobiSymmetricRaiseB β k
  let c := jacobiSymmetricRaiseA (β + k + 1 / 2) (n - k)
  let d := jacobiSymmetricRaiseB (β + k + 1 / 2) (n - k)
  have ha₀ := jacobiSymmetricRaiseA_pos hβ k
  have hc₀ := jacobiSymmetricRaiseA_pos ha (n - k)
  obtain ⟨hi, hb⟩ := jacobi_symmetric_raise_all hβ k
  obtain ⟨ho, hd⟩ := jacobi_symmetric_raise_all ha (n - k)
  change jacobi β β k = a • _ + b • _ at hi
  change jacobi _ _ (n - k) = c • _ + d • _ at ho
  change k < 2 → b = 0 at hb
  change n - k < 2 → d = 0 at hd
  have hp : β + k + 1 / 2 + 1 = β + 1 + k + 1 / 2 := by ring
  rw [hp] at ho
  have ho' := congrArg (fun p : ℝ[X] => p.eval₂ C (X 0 : MvPolynomial (Fin 2) ℝ)) ho
  simp only [Polynomial.smul_eq_C_mul, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C] at ho'
  have hi' := congrArg (diskLift k) hi
  rw [diskLift_add, diskLift_smul, diskLift_smul] at hi'
  by_cases hsmall : k < 2
  · rw [hb hsmall, zero_smul, add_zero] at hi'
    simp only [dunklXuDiskRaiseA, dunklXuDiskRaiseB, dunklXuDiskRaiseC,
      dunklXuDiskRaiseD, dite_eq_left hsmall]
    refine ⟨mul_pos ha₀ hc₀, ?_, ?_, by simp⟩
    · simp only [zero_smul, add_zero, dunklXuDisk, smul_eq_C_mul]
      rw [hi', ho']
      simp only [smul_eq_C_mul, map_mul]
      rw [show n - 2 - k = n - k - 2 by omega]
      ring
    · intro hn
      change a * d = 0
      rw [hd (by omega), mul_zero]
  · have hk2 : 2 ≤ k := by omega
    have hkcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      rw [Nat.cast_sub hk2, Nat.cast_ofNat]
    have hl : -1 < β + 1 + (k - 2 : ℕ) + 1 / 2 := by
      have := Nat.cast_nonneg (α := ℝ) (k - 2)
      linarith
    let e := jacobiSymmetricLowerA (β + 1 + (k - 2 : ℕ) + 1 / 2) (n - k)
    let f := jacobiSymmetricLowerB (β + 1 + (k - 2 : ℕ) + 1 / 2) (n - k)
    have hlower := jacobi_symmetric_weight_lower hl (n - k)
    change (1 - Polynomial.X ^ 2) * jacobi _ _ (n - k) = e • _ + f • _ at hlower
    rw [show β + 1 + (k - 2 : ℕ) + 1 / 2 + 1 = β + k + 1 / 2 by
      rw [hkcast]; ring] at hlower
    have hlower' := congrArg
      (fun p : ℝ[X] => p.eval₂ C (X 0 : MvPolynomial (Fin 2) ℝ)) hlower
    simp only [Polynomial.smul_eq_C_mul, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_sub, Polynomial.eval₂_one,
      Polynomial.eval₂_pow, Polynomial.eval₂_X] at hlower'
    have hLift : diskLift k (jacobi (β + 1) (β + 1) (k - 2)) =
        (1 - X 0 ^ 2) * diskLift (k - 2) (jacobi (β + 1) (β + 1) (k - 2)) := by
      convert diskLift_add_two (k - 2) (jacobi (β + 1) (β + 1) (k - 2))
        (natDegree_jacobi_le _ _ _) using 1
      congr 1
      omega
    rw [hLift] at hi'
    simp only [dunklXuDiskRaiseA, dunklXuDiskRaiseB, dunklXuDiskRaiseC,
      dunklXuDiskRaiseD, dite_eq_right hsmall]
    change 0 < a * c ∧ _ = (a * c) • _ + (a * d) • _ + (b * e) • _ + (b * f) • _ ∧ _
    refine ⟨mul_pos ha₀ hc₀, ?_, ?_, ?_⟩
    · simp only [dunklXuDisk, smul_eq_C_mul]
      rw [hi']
      simp only [smul_eq_C_mul]
      rw [show n - 2 - k = n - k - 2 by omega,
        show n - (k - 2) = n - k + 2 by omega,
        show n - 2 - (k - 2) = n - k by omega]
      calc
        _ = (C a * ((jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)).eval₂ C (X 0)) *
              diskLift k (jacobi (β + 1) (β + 1) k)) +
            C b * (((1 - X 0 ^ 2) *
              (jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)).eval₂ C (X 0)) *
              diskLift (k - 2) (jacobi (β + 1) (β + 1) (k - 2))) := by ring
        _ = _ := by rw [hlower', ho']; simp only [map_mul]; ring
    · intro hn
      change a * d = 0
      rw [hd (by omega), mul_zero]
    · intro h
      exact False.elim (hsmall h)

/-- The original support API follows from the explicit four coefficients. -/
theorem exists_dunklXuDisk_raise {β : ℝ} (hβ : -1 < β) (n k : ℕ) (hk : k ≤ n) :
    ∃ a b c d : ℝ, 0 < a ∧ dunklXuDisk β n k =
      a • dunklXuDisk (β + 1) n k + b • dunklXuDisk (β + 1) (n - 2) k +
      c • dunklXuDisk (β + 1) n (k - 2) + d • dunklXuDisk (β + 1) (n - 2) (k - 2) ∧
      (n < k + 2 → b = 0) ∧ (k < 2 → c = 0 ∧ d = 0) :=
  ⟨_, _, _, _, dunklXuDisk_raise hβ n k hk⟩

end MvPolynomial
