/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.ExtremeCertificate
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Finset.Sort

/-! # Alternation of finite norming certificates
A positive certificate annihilating degree-`n` polynomials needs at least `n+2`
points. At exactly that many ordered points its signs alternate (ATAP 10.1).
-/

public section
namespace Polynomial
open Set

/-- Moment annihilation implies annihilation of every polynomial in the degree space. -/
theorem sum_mul_eval_eq_zero_of_moments {ι : Type*} [Fintype ι] {n : ℕ}
    (x c : ι → ℝ) (h : ∀ j : Fin (n + 1), ∑ i, c i * x i ^ (j : ℕ) = 0)
    {p : ℝ[X]} (hp : p.degree ≤ n) : ∑ i, c i * p.eval (x i) = 0 := by
  have hp' : p ∈ degreeLT ℝ (n + 1) := mem_degreeLT.mpr
    (hp.trans_lt (by exact_mod_cast Nat.lt_succ_self n))
  simp_rw [eval_eq_sum_degreeLTEquiv hp', Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  calc
    _ = degreeLTEquiv ℝ (n + 1) ⟨p, hp'⟩ j * ∑ i, c i * x i ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [h j, mul_zero]

/-- An injective finite family in a linear order can be reindexed increasingly. -/
theorem exists_strictMono_reindex {α : Type*} [LinearOrder α] {m : ℕ}
    {x : Fin m → α} (hx : Function.Injective x) :
    ∃ e : Equiv.Perm (Fin m), StrictMono (x ∘ e) := by
  classical
  let s := Finset.univ.image x
  have hc : s.card = m := by simp [s, Finset.card_image_of_injective _ hx]
  let f : Fin m ≃ s := Equiv.ofBijective (fun i ↦ ⟨x i, by simp [s]⟩) (by
    constructor
    · intro i j h
      exact hx (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨i, rfl⟩)
  let e := (s.orderIsoOfFin hc).toEquiv.trans f.symm
  refine ⟨e, ?_⟩
  intro i j hij
  have hi : x (e i) = (s.orderIsoOfFin hc i : α) := congrArg Subtype.val (f.apply_symm_apply _)
  have hj : x (e j) = (s.orderIsoOfFin hc j : α) := congrArg Subtype.val (f.apply_symm_apply _)
  change x (e i) < x (e j)
  rw [hi, hj]
  exact (s.orderIsoOfFin hc).strictMono hij

/-- A nontrivial annihilating functional on distinct nodes needs more than
`n+1` nodes. This is the Haar property for polynomial evaluation (ATAP 10.1). -/
theorem card_ge_of_nonzero_annihilating_weights {m n : ℕ} {x c : Fin m → ℝ}
    (hx : Function.Injective x) (hc : ∀ i, c i ≠ 0) (hm : 0 < m)
    (hz : ∀ p : ℝ[X], p.degree ≤ n → ∑ i, c i * p.eval (x i) = 0) :
    n + 2 ≤ m := by
  classical
  by_contra h
  let i : Fin m := ⟨0, hm⟩
  let p := Lagrange.basis Finset.univ x i
  have hp : p.degree ≤ n := by
    rw [Lagrange.degree_basis hx.injOn (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (show m - 1 ≤ n by omega)
  have ht := hz p hp
  have he : ∑ j, c j * p.eval (x j) = c i := by
    rw [Finset.sum_eq_single i]
    · simp [p, Lagrange.eval_basis_self hx.injOn]
    · intro j _ hji
      simp [p, Lagrange.eval_basis_of_ne hji.symm]
    · simp
  exact hc i (he.symm.trans ht)

/-- At `n+2` increasing nodes, nonzero weights annihilating degree-`n`
polynomials have opposite signs at adjacent nodes (ATAP 10.1). -/
theorem mul_weights_neg_of_annihilating {n : ℕ} {x c : Fin (n + 2) → ℝ}
    (hx : StrictMono x) (hc : ∀ i, c i ≠ 0)
    (hz : ∀ p : ℝ[X], p.degree ≤ n → ∑ i, c i * p.eval (x i) = 0)
    (i : Fin (n + 1)) : c i.castSucc * c i.succ < 0 := by
  classical
  let s := (Finset.univ.erase i.castSucc).erase i.succ
  let p : ℝ[X] := ∏ j ∈ s, (X - C (x j))
  have hne : i.castSucc ≠ i.succ := ne_of_lt Fin.castSucc_lt_succ
  have hcard : s.card = n := by simp [s, hne.symm]
  have hp : p.degree ≤ n := by
    simp [p, degree_prod, hcard]
  have hzero (j : Fin (n + 2)) (hj : j ∈ s) : p.eval (x j) = 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero hj (sub_self _)
  have htwo : c i.castSucc * p.eval (x i.castSucc) + c i.succ * p.eval (x i.succ) = 0 := by
    have ht := hz p hp
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i.castSucc),
      ← Finset.add_sum_erase _ _ (show i.succ ∈ Finset.univ.erase i.castSucc by simp [hne.symm])] at ht
    have hr : ∑ j ∈ s, c j * p.eval (x j) = 0 := Finset.sum_eq_zero (fun j hj ↦ by rw [hzero j hj, mul_zero])
    change _ + (_ + ∑ j ∈ s, c j * p.eval (x j)) = 0 at ht
    rwa [hr, add_zero] at ht
  have hprod : 0 < p.eval (x i.castSucc) * p.eval (x i.succ) := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C, ← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro j hj
    have hj1 : j ≠ i.castSucc := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hj2 : j ≠ i.succ := (Finset.mem_erase.mp hj).1
    have hji : j < i.castSucc ∨ i.succ < j := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hj1 hj2
      change (j : ℕ) < (i : ℕ) ∨ (i : ℕ) + 1 < (j : ℕ)
      omega
    rcases hji with h | h
    · exact mul_pos (sub_pos.mpr (hx h))
        (sub_pos.mpr (hx (h.trans Fin.castSucc_lt_succ)))
    · exact mul_pos_of_neg_of_neg
        (sub_neg.mpr (hx (Fin.castSucc_lt_succ.trans h))) (sub_neg.mpr (hx h))
  have hn : c i.castSucc * p.eval (x i.castSucc) ≠ 0 :=
    mul_ne_zero (hc _) (by intro h; rw [h, zero_mul] at hprod; exact (lt_irrefl 0) hprod)
  have hsq : 0 < (c i.castSucc * p.eval (x i.castSucc)) ^ 2 := sq_pos_of_ne_zero hn
  have hh : (c i.castSucc * c i.succ) * (p.eval (x i.castSucc) * p.eval (x i.succ)) < 0 := by
    have hj : c i.succ * p.eval (x i.succ) = -(c i.castSucc * p.eval (x i.castSucc)) := by linarith
    calc
      _ = (c i.castSucc * p.eval (x i.castSucc)) * (c i.succ * p.eval (x i.succ)) := by ring
      _ = -((c i.castSucc * p.eval (x i.castSucc)) ^ 2) := by rw [hj]; ring
      _ < 0 := neg_neg_of_pos hsq
  by_contra h
  exact (not_le_of_gt hh) (mul_nonneg (le_of_not_gt h) hprod.le)

end Polynomial
