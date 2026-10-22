/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.Alternation
public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Equioscillation certificates for real polynomial approximation
The alternation criterion and the de la Vallée Poussin lower bound use the
supremum norm on a compact interval. Reference: ATAP, Theorem 10.1, Exercise 10.3.
-/

@[expose] public section
namespace Polynomial
open Set

/-- An error curve attains its uniform norm with alternating signs at `n+2`
strictly increasing points. The zero-error case is included (ATAP 10.1). -/
def Equioscillates {a b : ℝ} (n : ℕ) (e : C(Icc a b, ℝ)) : Prop :=
  ∃ (x : Fin (n + 2) → Icc a b) (σ : ℝ), StrictMono x ∧ |σ| = 1 ∧
    ∀ i, e (x i) = σ * (-1 : ℝ) ^ (i : ℕ) * ‖e‖

/-- Alternating errors of magnitude at least `L` certify a lower bound for
all degree-`n` competitors (de la Vallée Poussin, ATAP Exercise 10.3). -/
theorem lower_bound_of_alternating_error {a b L : ℝ} {n : ℕ}
    {f : C(Icc a b, ℝ)} {p : ℝ[X]} (hp : p.degree ≤ n)
    {x : Fin (n + 2) → Icc a b} (hx : StrictMono x) {σ : ℝ} (hσ : |σ| = 1)
    (he : ∀ i : Fin (n + 2), L ≤ σ * (-1 : ℝ) ^ (i : ℕ) * (f (x i) - p.eval (x i : ℝ)))
    {q : ℝ[X]} (hq : q.degree ≤ n) : L ≤ ‖f - q.toContinuousMapOn (Icc a b)‖ := by
  by_contra h
  have hlt : ‖f - q.toContinuousMapOn (Icc a b)‖ < L := lt_of_not_ge h
  let d := q - p
  have hpos (i : Fin (n + 2)) : 0 < σ * (-1 : ℝ) ^ (i : ℕ) * d.eval (x i : ℝ) := by
    have hn := (f - q.toContinuousMapOn (Icc a b)).norm_coe_le_norm (x i)
    have ht : |σ * (-1 : ℝ) ^ (i : ℕ) * (f (x i) - q.eval (x i : ℝ))| < L := by
      simpa only [abs_mul, hσ, abs_neg_one_pow, one_mul, Real.norm_eq_abs,
        ContinuousMap.sub_apply, toContinuousMapOn_apply, toContinuousMap_apply] using hn.trans_lt hlt
    have hl := (abs_lt.mp ht).2
    have hh := he i
    dsimp [d]
    rw [eval_sub]
    nlinarith
  have hσ2 : σ * σ = 1 := by nlinarith [sq_abs σ]
  have hsign (i : Fin (n + 1)) :
      d.eval (x i.castSucc : ℝ) * d.eval (x i.succ : ℝ) < 0 := by
    have hm := mul_pos (hpos i.castSucc) (hpos i.succ)
    have heq : (σ * (-1 : ℝ) ^ (i.castSucc : ℕ)) *
        (σ * (-1 : ℝ) ^ (i.succ : ℕ)) = -1 := by
      simp only [Fin.val_castSucc, Fin.val_succ, pow_succ]
      calc _ = -(σ * σ) * ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) := by ring
           _ = -1 := by rw [hσ2, ← mul_pow]; simp
    have heq' : (σ * (-1 : ℝ) ^ (i.castSucc : ℕ) * d.eval (x i.castSucc : ℝ)) *
        (σ * (-1 : ℝ) ^ (i.succ : ℕ) * d.eval (x i.succ : ℝ)) =
        -(d.eval (x i.castSucc : ℝ) * d.eval (x i.succ : ℝ)) := by
      calc _ = ((σ * (-1 : ℝ) ^ (i.castSucc : ℕ)) *
            (σ * (-1 : ℝ) ^ (i.succ : ℕ))) *
            (d.eval (x i.castSucc : ℝ) * d.eval (x i.succ : ℝ)) := by ring
           _ = _ := by rw [heq]; ring
    rw [heq'] at hm
    linarith
  have hd := le_natDegree_of_alternating_eval
    (x := fun i ↦ (x i : ℝ)) (fun _ _ h ↦ hx h) hsign
  have hdeg : d.natDegree ≤ n := natDegree_le_of_degree_le ((degree_sub_le q p).trans (max_le hq hp))
  omega

/-- An equioscillating error curve certifies a best polynomial approximation
(ATAP, the sufficient direction of Theorem 10.1). -/
theorem Equioscillates.norm_sub_le {a b : ℝ} {n : ℕ}
    {f : C(Icc a b, ℝ)} {p : ℝ[X]} (hp : p.degree ≤ n)
    (he : Equioscillates n (f - p.toContinuousMapOn (Icc a b)))
    {q : ℝ[X]} (hq : q.degree ≤ n) :
    ‖f - p.toContinuousMapOn (Icc a b)‖ ≤ ‖f - q.toContinuousMapOn (Icc a b)‖ := by
  obtain ⟨x, σ, hx, hσ, he⟩ := he
  apply lower_bound_of_alternating_error hp hx hσ _ hq
  intro i
  have hi := he i
  change f (x i) - p.eval (x i : ℝ) = _ at hi
  rw [hi]
  have hσ2 : σ * σ = 1 := by nlinarith [sq_abs σ]
  have hpow : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by rw [← mul_pow]; simp
  apply le_of_eq
  calc
    _ = (σ * σ) * ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) *
        ‖f - p.toContinuousMapOn (Icc a b)‖ := by rw [hσ2, hpow]; ring
    _ = _ := by ring

end Polynomial
