/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Polynomial.Equioscillation
public import LeanFun.Mathlib.Analysis.Polynomial.FiniteAlternation

/-! # Equioscillation characterization
A real polynomial on a nondegenerate compact interval is a best uniform
approximant exactly when its error equioscillates. Reference: ATAP, Theorem 10.1.
-/

public section
namespace Polynomial
open Set

private theorem equioscillates_of_nonzero_minimal_error {a b : ℝ} {n : ℕ}
    (e : C(Icc a b, ℝ)) (he : 0 < ‖e‖)
    (hmin : ∀ q : ℝ[X], q.degree ≤ n → ‖e‖ ≤ ‖e - q.toContinuousMapOn (Icc a b)‖) :
    Equioscillates n e := by
  obtain ⟨m, x, w, hm, hx, hw, hsum, hxe, hmoment⟩ := exists_extremeMoment_certificate e he hmin
  have hm0 : 0 < m := by
    by_contra h
    have hmz : m = 0 := by omega
    subst m
    simp at hsum
  let c := fun i ↦ w i * e (x i)
  have hc (i : Fin m) : c i ≠ 0 := mul_ne_zero (hw i).ne' (by
    intro h
    have h' := hxe i
    rw [h, abs_zero] at h'
    linarith)
  have hz (p : ℝ[X]) (hp : p.degree ≤ n) : ∑ i, c i * p.eval (x i : ℝ) = 0 := by
    apply sum_mul_eval_eq_zero_of_moments (fun i ↦ (x i : ℝ)) c _ hp
    intro j
    have h := congrFun hmoment j
    simpa only [extremeMoment, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, c, mul_assoc] using h
  have hcard := card_ge_of_nonzero_annihilating_weights
    (x := fun i ↦ (x i : ℝ)) (Subtype.val_injective.comp hx) hc hm0 hz
  have hm' : m = n + 2 := by omega
  subst m
  obtain ⟨r, hr⟩ := exists_strictMono_reindex hx
  let y := x ∘ r
  have hy : StrictMono (fun i ↦ (y i : ℝ)) := fun _ _ hij ↦ hr hij
  have hyabs (i : Fin (n + 2)) : |e (y i)| = ‖e‖ := hxe (r i)
  have hneg (i : Fin (n + 1)) : e (y i.castSucc) * e (y i.succ) < 0 := by
    have hz' (p : ℝ[X]) (hp : p.degree ≤ n) :
        ∑ i, c (r i) * p.eval (y i : ℝ) = 0 := by
      exact (Equiv.sum_comp r (fun i ↦ c i * p.eval (x i : ℝ))).trans (hz p hp)
    have ht := mul_weights_neg_of_annihilating hy (fun i ↦ hc (r i)) hz' i
    have hwprod : 0 < w (r i.castSucc) * w (r i.succ) := mul_pos (hw _) (hw _)
    have ht' : (w (r i.castSucc) * w (r i.succ)) *
        (e (y i.castSucc) * e (y i.succ)) < 0 := by
      convert ht using 1
      dsimp [c, y, Function.comp_apply]
      ring
    by_contra h
    exact (not_le_of_gt ht') (mul_nonneg hwprod.le (le_of_not_gt h))
  have hnext (i : Fin (n + 1)) : e (y i.succ) = -e (y i.castSucc) := by
    rcases abs_eq_abs.mp ((hyabs i.succ).trans (hyabs i.castSucc).symm) with h | h
    · have ht := hneg i
      rw [h] at ht
      nlinarith [sq_nonneg (e (y i.castSucc))]
    · exact h
  refine ⟨y, e (y 0) / ‖e‖, hr, ?_, ?_⟩
  · rw [abs_div, hyabs, abs_of_pos he, div_self he.ne']
  · intro i
    induction i using Fin.induction with
    | zero => simp [div_mul_cancel₀ _ he.ne']
    | succ i ih => rw [hnext i, ih]; simp [pow_succ]

/-- Every real best approximant on a nondegenerate interval has `n+2`
alternating extrema, including the exact-polynomial case (ATAP 10.1). -/
theorem equioscillates_of_bestApproximation {a b : ℝ} (hab : a < b) {n : ℕ}
    (f : C(Icc a b, ℝ)) {p : ℝ[X]} (hp : p.degree ≤ n)
    (hmin : ∀ q : ℝ[X], q.degree ≤ n →
      ‖f - p.toContinuousMapOn (Icc a b)‖ ≤ ‖f - q.toContinuousMapOn (Icc a b)‖) :
    Equioscillates n (f - p.toContinuousMapOn (Icc a b)) := by
  let e := f - p.toContinuousMapOn (Icc a b)
  by_cases he : ‖e‖ = 0
  · have he0 : e = 0 := norm_eq_zero.mp he
    let x (i : Fin (n + 2)) : Icc a b :=
      ⟨a + (b - a) * (i : ℕ) / (n + 1), by
        have hi : (i : ℝ) ≤ n + 1 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
        constructor
        · exact le_add_of_nonneg_right (div_nonneg
            (mul_nonneg (sub_nonneg.mpr hab.le) (Nat.cast_nonneg _)) (by positivity))
        · have hd : (0 : ℝ) < n + 1 := by positivity
          have hh := (div_le_iff₀ hd).2 (mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab.le))
          linarith⟩
    have hx : StrictMono x := by
      intro i j hij
      change a + (b - a) * (i : ℕ) / (n + 1) < a + (b - a) * (j : ℕ) / (n + 1)
      gcongr
      exact_mod_cast hij
    refine ⟨x, 1, hx, by norm_num, ?_⟩
    intro i
    change e (x i) = 1 * (-1 : ℝ) ^ (i : ℕ) * ‖e‖
    rw [he0]
    simp
  · apply equioscillates_of_nonzero_minimal_error e (lt_of_le_of_ne (norm_nonneg _) (Ne.symm he))
    intro q hq
    have h := hmin (p + q) ((degree_add_le _ _).trans (max_le hp hq))
    have heq : (p + q).toContinuousMapOn (Icc a b) =
        p.toContinuousMapOn (Icc a b) + q.toContinuousMapOn (Icc a b) := by ext x; simp
    simpa only [e, heq, sub_add_eq_sub_sub] using h

/-- The real equioscillation characterization of best polynomial approximation
on any nondegenerate compact interval (ATAP, Theorem 10.1). -/
theorem equioscillates_iff_bestApproximation {a b : ℝ} (hab : a < b) {n : ℕ}
    (f : C(Icc a b, ℝ)) {p : ℝ[X]} (hp : p.degree ≤ n) :
    Equioscillates n (f - p.toContinuousMapOn (Icc a b)) ↔
      ∀ q : ℝ[X], q.degree ≤ n →
        ‖f - p.toContinuousMapOn (Icc a b)‖ ≤ ‖f - q.toContinuousMapOn (Icc a b)‖ :=
  ⟨fun h _ hq ↦ h.norm_sub_le hp hq, equioscillates_of_bestApproximation hab f hp⟩

end Polynomial
