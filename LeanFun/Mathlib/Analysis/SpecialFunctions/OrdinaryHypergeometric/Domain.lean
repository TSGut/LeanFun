/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Classical Gauss-series inputs
Every nonzero numerator coefficient has a nonzero denominator. Termination
is taken before a later denominator pole, with the finite-polynomial meaning
of DLMF 15.2.4--15.2.5 (including coincident terminating parameters). This is
not diagonal parameter cancellation (DLMF 15.2.6). Values use natural-order
convergence and hence include conditional convergence on the unit circle.
-/
@[expose] public noncomputable section
open Polynomial Filter
open scoped Topology
section Coefficients
variable {K : Type*} [Field K] [CharZero K]

/-- Parameters for which no nonzero Gauss coefficient encounters a denominator pole. -/
structure GaussParameters (K : Type*) [Field K] [CharZero K] where
  a : K
  b : K
  c : K
  denominator : ∀ n : ℕ, (ascPochhammer K n).eval c = 0 →
    (ascPochhammer K n).eval a * (ascPochhammer K n).eval b = 0

/-- Classical coefficients stop at numerator termination, before any undefined
quotient is formed. All remaining denominators are nonzero. -/
def ordinaryHypergeometricCoefficientOn (p : GaussParameters K) (n : ℕ) : K := by
  classical
  exact if (ascPochhammer K n).eval p.a * (ascPochhammer K n).eval p.b = 0 then 0 else
    ((ascPochhammer K n).eval p.a * (ascPochhammer K n).eval p.b) /
      ((ascPochhammer K n).eval p.c * (n.factorial : K))

/-- A nonzero numerator coefficient has a genuine denominator. -/
theorem GaussParameters.denominator_ne_zero (p : GaussParameters K) (n : ℕ)
    (h : (ascPochhammer K n).eval p.a * (ascPochhammer K n).eval p.b ≠ 0) :
    (ascPochhammer K n).eval p.c * (n.factorial : K) ≠ 0 := by
  exact mul_ne_zero (fun hc ↦ h (p.denominator n hc)) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)

/-- Numerator termination gives the genuine zero coefficients of a polynomial. -/
theorem ordinaryHypergeometricCoefficientOn_eq_zero (p : GaussParameters K) (n : ℕ)
    (h : (ascPochhammer K n).eval p.a * (ascPochhammer K n).eval p.b = 0) :
    ordinaryHypergeometricCoefficientOn p n = 0 := by
  simp only [ordinaryHypergeometricCoefficientOn, h, ite_true]

/-- Away from a denominator pole, the coefficient is its classical quotient. -/
theorem ordinaryHypergeometricCoefficientOn_eq_div (p : GaussParameters K) (n : ℕ)
    (_h : (ascPochhammer K n).eval p.c ≠ 0) :
    ordinaryHypergeometricCoefficientOn p n =
      ((ascPochhammer K n).eval p.a * (ascPochhammer K n).eval p.b) /
        ((ascPochhammer K n).eval p.c * (n.factorial : K)) := by
  classical
  unfold ordinaryHypergeometricCoefficientOn
  split_ifs with h
  · rw [h, zero_div]
  · rfl


/-- Denominator parameters away from all poles always give admissible data. -/
def GaussParameters.ofNoPole (a b c : K) (hc : ∀ k : ℕ, c ≠ -(k : K)) :
    GaussParameters K := ⟨a, b, c, fun n hn ↦ by
  obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n c).mp hn
  exact False.elim (hc k ((neg_neg c).symm.trans (congrArg Neg.neg hk.symm)))⟩

/-- A terminating second numerator needs denominators only through its final degree. -/
def GaussParameters.ofTerminatingRight (a c : K) (k : ℕ)
    (hc : ∀ n ≤ k, (ascPochhammer K n).eval c ≠ 0) : GaussParameters K :=
  ⟨a, -(k : K), c, fun n hn ↦ by
    by_cases h : n ≤ k
    · exact False.elim (hc n h hn)
    · have hz : (ascPochhammer K n).eval (-(k : K)) = 0 :=
        (ascPochhammer_eval_eq_zero_iff n (-(k : K))).mpr ⟨k, by omega, by simp⟩
      rw [hz, mul_zero]⟩

/-- Exchanging the numerator parameters preserves admissibility. -/
def GaussParameters.swap (p : GaussParameters K) : GaussParameters K :=
  ⟨p.b, p.a, p.c, fun n hn ↦ by simpa only [mul_comm] using p.denominator n hn⟩

/-- The symmetric terminating constructor also covers earlier termination of the first numerator. -/
def GaussParameters.ofTerminatingLeft (b c : K) (k : ℕ)
    (hc : ∀ n ≤ k, (ascPochhammer K n).eval c ≠ 0) : GaussParameters K :=
  (GaussParameters.ofTerminatingRight b c k hc).swap

end Coefficients

section Values
variable {K : Type*} [RCLike K]

/-- All points where the naturally ordered classical Gauss series converges. -/
abbrev GaussSeriesPoint (p : GaussParameters K) :=
  {z : K // ∃ s : K, Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
    ordinaryHypergeometricCoefficientOn p n * z ^ n) atTop (𝓝 s)}

/-- The classical Gauss-series value on its exact convergence domain. -/
def ordinaryHypergeometricOn (p : GaussParameters K) (z : GaussSeriesPoint p) : K :=
  z.property.choose

/-- Its natural-order partial sums converge to the selected value. -/
theorem tendsto_ordinaryHypergeometricOn (p : GaussParameters K) (z : GaussSeriesPoint p) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
      ordinaryHypergeometricCoefficientOn p n * z.val ^ n) atTop
      (𝓝 (ordinaryHypergeometricOn p z)) := z.property.choose_spec

/-- Any convergent natural-order series gives the same classical value. -/
theorem ordinaryHypergeometricOn_eq_of_tendsto (p : GaussParameters K) (z : GaussSeriesPoint p)
    {s : K} (hs : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
      ordinaryHypergeometricCoefficientOn p n * z.val ^ n) atTop (𝓝 s)) :
    ordinaryHypergeometricOn p z = s :=
  tendsto_nhds_unique (tendsto_ordinaryHypergeometricOn p z) hs

/-- Unconditional summability supplies a classical series point. -/
def GaussSeriesPoint.ofHasSum (p : GaussParameters K) {z s : K}
    (hs : HasSum (fun n ↦ ordinaryHypergeometricCoefficientOn p n * z ^ n) s) :
    GaussSeriesPoint p := ⟨z, s, hs.tendsto_sum_nat⟩

/-- The supplied unconditional sum is the classical value. -/
theorem ordinaryHypergeometricOn_ofHasSum (p : GaussParameters K) {z s : K}
    (hs : HasSum (fun n ↦ ordinaryHypergeometricCoefficientOn p n * z ^ n) s) :
    ordinaryHypergeometricOn p (.ofHasSum p hs) = s :=
  ordinaryHypergeometricOn_eq_of_tendsto p _ hs.tendsto_sum_nat

/-- A terminating numerator makes every later classical coefficient zero. -/
theorem ordinaryHypergeometricCoefficientOn_eq_zero_of_termination
    (p : GaussParameters K) {k n : ℕ} (hk : p.a = -(k : K) ∨ p.b = -(k : K))
    (hn : k < n) : ordinaryHypergeometricCoefficientOn p n = 0 := by
  apply ordinaryHypergeometricCoefficientOn_eq_zero
  have h : (ascPochhammer K n).eval (-(k : K)) = 0 :=
    (ascPochhammer_eval_eq_zero_iff n (-(k : K))).mpr ⟨k, hn, by simp⟩
  rcases hk with hk | hk
  · rw [hk, h, zero_mul]
  · rw [hk, h, mul_zero]

/-- Every argument is a genuine convergence point for an admissible terminating series. -/
def GaussSeriesPoint.ofTerminating (p : GaussParameters K) (k : ℕ)
    (hk : p.a = -(k : K) ∨ p.b = -(k : K)) (z : K) : GaussSeriesPoint p :=
  .ofHasSum p (z := z) (hasSum_sum_of_ne_finset_zero (s := Finset.range (k + 1)) (fun n hn ↦ by
    rw [ordinaryHypergeometricCoefficientOn_eq_zero_of_termination p hk
      (by simpa using hn), zero_mul]))

/-- The terminating value is precisely its finite polynomial sum. -/
theorem ordinaryHypergeometricOn_terminating (p : GaussParameters K) (k : ℕ)
    (hk : p.a = -(k : K) ∨ p.b = -(k : K)) (z : K) :
    ordinaryHypergeometricOn p (.ofTerminating p k hk z) =
      ∑ n ∈ Finset.range (k + 1), ordinaryHypergeometricCoefficientOn p n * z ^ n :=
  ordinaryHypergeometricOn_ofHasSum p _

end Values

section ShiftParameters
variable {K : Type*} [Field K] [CharZero K]
/-- A nonconstant admissible Gauss series has a nonzero first denominator. -/
theorem GaussParameters.c_ne_zero (p : GaussParameters K) (h : p.a * p.b ≠ 0) :
    p.c ≠ 0 := by
  intro hc
  have hz := p.denominator 1 (by simpa using hc)
  simp only [ascPochhammer_one, eval_X] at hz
  exact h hz

/-- Shifting nonconstant admissible data does not cross a denominator pole before termination. -/
def GaussParameters.shift (p : GaussParameters K) (h : p.a * p.b ≠ 0) :
    GaussParameters K := ⟨p.a + 1, p.b + 1, p.c + 1, fun n hn ↦ by
  have hc : (ascPochhammer K (n + 1)).eval p.c = 0 := by
    simp only [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_one]
    rw [hn, mul_zero]
  have hz := p.denominator (n + 1) hc
  simp only [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_one] at hz
  apply (mul_eq_zero.mp (show (p.a * p.b) *
    ((ascPochhammer K n).eval (p.a + 1) * (ascPochhammer K n).eval (p.b + 1)) = 0 by
    convert hz using 1; ring)).resolve_left h⟩

/-- The constant case is handled without evaluating any undefined shifted function. -/
theorem ordinaryHypergeometricCoefficientOn_succ_of_constant (p : GaussParameters K)
    (h : p.a * p.b = 0) (n : ℕ) :
    ordinaryHypergeometricCoefficientOn p (n + 1) = 0 := by
  apply ordinaryHypergeometricCoefficientOn_eq_zero
  simp only [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_one]
  calc
    _ = (p.a * p.b) * ((ascPochhammer K n).eval (p.a + 1) *
      (ascPochhammer K n).eval (p.b + 1)) := by ring
    _ = 0 := by rw [h, zero_mul]

/-- The classical derivative-coefficient identity for nonconstant admissible data. -/
theorem ordinaryHypergeometricCoefficientOn_shift (p : GaussParameters K)
    (h : p.a * p.b ≠ 0) (n : ℕ) :
    ((n : K) + 1) * ordinaryHypergeometricCoefficientOn p (n + 1) =
      (p.a * p.b / p.c) * ordinaryHypergeometricCoefficientOn (p.shift h) n := by
  have hn1 : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hnum : (ascPochhammer K (n + 1)).eval p.a * (ascPochhammer K (n + 1)).eval p.b =
      (p.a * p.b) * ((ascPochhammer K n).eval (p.shift h).a *
        (ascPochhammer K n).eval (p.shift h).b) := by
    simp only [GaussParameters.shift, ascPochhammer_succ_left, eval_mul,
      eval_X, eval_comp, eval_add, eval_one]
    ring
  by_cases hz : (ascPochhammer K n).eval (p.shift h).a *
      (ascPochhammer K n).eval (p.shift h).b = 0
  · rw [ordinaryHypergeometricCoefficientOn_eq_zero (p.shift h) n hz,
      ordinaryHypergeometricCoefficientOn_eq_zero p (n + 1) (by rw [hnum, hz, mul_zero])]
    simp only [mul_zero]
  · have hc : (ascPochhammer K n).eval (p.shift h).c ≠ 0 :=
      fun he ↦ hz ((p.shift h).denominator n he)
    have hc0 := p.c_ne_zero h
    have hcn : (ascPochhammer K (n + 1)).eval p.c ≠ 0 := by
      simpa only [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp,
        eval_add, eval_one, GaussParameters.shift] using mul_ne_zero hc0 hc
    rw [ordinaryHypergeometricCoefficientOn_eq_div p (n + 1) hcn,
      ordinaryHypergeometricCoefficientOn_eq_div (p.shift h) n hc, hnum]
    simp only [GaussParameters.shift, ascPochhammer_succ_left, eval_mul, eval_X,
      eval_comp, eval_add, eval_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one] at hc ⊢
    field_simp

end ShiftParameters
