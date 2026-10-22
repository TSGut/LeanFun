/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Roots

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Finset.Max

/-!
# Strict separation of consecutive orthogonal polynomial roots

Consecutive members have no common roots and their real roots separate each other.
Together with the simple-root counts `n` and `n+1`, this gives strict interlacing.
References: Szegő, Chapter 3; DLMF 18.2(vi), https://dlmf.nist.gov/18.2#vi.
-/

public section

open MeasureTheory Set

/-- The smaller separating set cannot reach the leftmost point of the larger set.
This is the finite-order counting argument for outer roots (Szegő, Chapter 3). -/
private theorem exists_mem_lt_all_of_separates {α : Type*} [LinearOrder α]
    (s t : Finset α) (hc : s.card < t.card)
    (hsep : ∀ b ∈ t, ∀ c ∈ t, b < c → ∃ d ∈ s, b < d ∧ d < c) :
    ∃ b ∈ t, ∀ a ∈ s, b < a := by
  classical
  have ht : t.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨t.min' ht, t.min'_mem ht, ?_⟩
  intro a ha
  by_contra h
  have hab : ∀ b ∈ t, a ≤ b := fun b hb ↦
    (le_of_not_gt h).trans (t.min'_le b hb)
  have hn (b : t) : (s.filter (· ≤ b.val)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, hab b.val b.property⟩⟩
  let f : t → s := fun b ↦ ⟨(s.filter (· ≤ b.val)).max' (hn b),
    (Finset.mem_filter.mp ((s.filter (· ≤ b.val)).max'_mem (hn b))).1⟩
  have hf : StrictMono f := by
    intro b c hbc
    obtain ⟨d, hd, hbd, hdc⟩ := hsep b.val b.property c.val c.property hbc
    have hb : (f b).val ≤ b.val :=
      (Finset.mem_filter.mp ((s.filter (· ≤ b.val)).max'_mem (hn b))).2
    have hd' : d ≤ (f c).val :=
      (s.filter (· ≤ c.val)).le_max' d (Finset.mem_filter.mpr ⟨hd, hdc.le⟩)
    exact (hb.trans_lt hbd).trans_le hd'
  exact (not_le_of_gt hc) (Finset.card_le_card_of_injective hf.injective)

namespace Polynomial

/-- A nowhere-zero Wronskian forces a zero of the denominator between two zeros
of the numerator. This is the Rolle argument behind the separation theorem
(Szegő, Chapter 3). -/
theorem exists_eval_eq_zero_between_of_wronskian_ne_zero {p q : ℝ[X]}
    (hw : ∀ x : ℝ, p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x ≠ 0)
    {a b : ℝ} (hab : a < b) (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ c ∈ Ioo a b, q.eval c = 0 := by
  by_contra hno
  push Not at hno
  have hq : ∀ x ∈ Icc a b, q.eval x ≠ 0 := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      intro h
      exact hw a (by rw [ha, h]; ring)
    by_cases hxb : x = b
    · subst x
      intro h
      exact hw b (by rw [hb, h]; ring)
    exact hno x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  obtain ⟨c, hc, hd⟩ := exists_hasDerivAt_eq_zero hab
    (p.differentiable.continuous.continuousOn.div
      q.differentiable.continuous.continuousOn hq)
    (show p.eval a / q.eval a = p.eval b / q.eval b by rw [ha, hb]; simp)
    (fun x hx => (p.hasDerivAt x).div (q.hasDerivAt x) (hq x (Ioo_subset_Icc_self hx)))
  exact hw c ((div_eq_zero_iff).mp hd |>.resolve_right
    (pow_ne_zero 2 (hq c (Ioo_subset_Icc_self hc))))

namespace Sequence

/-- Between two distinct roots of `P n` there is a root of `P (n+1)`
(DLMF 18.2(vi)). -/
theorem IsOrthogonal.exists_root_succ_between {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ)
    {a b : ℝ} (hab : a < b) (ha : (P n).eval a = 0) (hb : (P n).eval b = 0) :
    ∃ c ∈ Ioo a b, (P (n + 1)).eval c = 0 := by
  apply exists_eval_eq_zero_between_of_wronskian_ne_zero _ hab ha hb
  intro x heq
  apply hP.wronskian_ne_zero hμ hpos n x
  nlinarith

/-- Between two distinct roots of `P (n+1)` there is a root of `P n`
(DLMF 18.2(vi)). -/
theorem IsOrthogonal.exists_root_between_succ {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ)
    {a b : ℝ} (hab : a < b) (ha : (P (n + 1)).eval a = 0)
    (hb : (P (n + 1)).eval b = 0) : ∃ c ∈ Ioo a b, (P n).eval c = 0 := by
  apply exists_eval_eq_zero_between_of_wronskian_ne_zero _ hab ha hb
  intro x heq
  apply hP.wronskian_ne_zero hμ hpos n x
  nlinarith

/-- The degree-`n+1` polynomial has a root strictly below every root of the degree-`n`
polynomial, and a distinct root strictly above every such root (DLMF 18.2(vi)). -/
theorem IsOrthogonal.exists_outer_roots {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ a b : ℝ, a < b ∧ (P (n + 1)).eval a = 0 ∧ (P (n + 1)).eval b = 0 ∧
      ∀ x : ℝ, (P n).eval x = 0 → a < x ∧ x < b := by
  classical
  let s := (P n).roots.toFinset
  let t := (P (n + 1)).roots.toFinset
  have hs (x : ℝ) : x ∈ s ↔ (P n).eval x = 0 := by
    simp only [s, Multiset.mem_toFinset, mem_roots (P.ne_zero n), IsRoot]
  have ht (x : ℝ) : x ∈ t ↔ (P (n + 1)).eval x = 0 := by
    simp only [t, Multiset.mem_toFinset, mem_roots (P.ne_zero (n + 1)), IsRoot]
  have hc : s.card < t.card := by
    dsimp [s, t]
    rw [Multiset.toFinset_card_of_nodup (hP.roots_nodup hμ hpos n),
      Multiset.toFinset_card_of_nodup (hP.roots_nodup hμ hpos (n + 1)),
      hP.card_roots hμ hpos n, hP.card_roots hμ hpos (n + 1)]
    omega
  have hsep : ∀ a ∈ t, ∀ b ∈ t, a < b → ∃ c ∈ s, a < c ∧ c < b := by
    intro a ha b hb hab
    obtain ⟨c, hc, hz⟩ := hP.exists_root_between_succ hμ hpos n hab
      ((ht a).mp ha) ((ht b).mp hb)
    exact ⟨c, (hs c).mpr hz, hc⟩
  obtain ⟨a, ha, hal⟩ := exists_mem_lt_all_of_separates s t hc hsep
  obtain ⟨b, hb, hbr⟩ := exists_mem_lt_all_of_separates
    (α := OrderDual ℝ) s t hc (by
      intro u hu v hv hvu
      obtain ⟨c, hc, hvc, hcu⟩ := hsep v hv u hu hvu
      exact ⟨c, hc, hcu, hvc⟩)
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < (P n).roots.card by
    rw [hP.card_roots hμ hpos n]
    omega)
  have hxs : x ∈ s := Multiset.mem_toFinset.mpr hx
  exact ⟨a, b, (hal x hxs).trans (hbr x hxs), (ht a).mp ha, (ht b).mp hb,
    fun x hx ↦ ⟨hal x ((hs x).mpr hx), hbr x ((hs x).mpr hx)⟩⟩

end Sequence
end Polynomial
