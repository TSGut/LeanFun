/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.Domain
/-! # Finite admissibility for terminating Gauss parameters
Only denominator factors before termination are required. Quadratic numerator
pairs terminate at the half-degree. References: DLMF15.2.4--5 and18.5.10.
-/
@[expose] public noncomputable section
open Polynomial Filter
open scoped Topology
section Parameters
variable {K : Type*} [Field K]

/-- Finite denominator admissibility passes to every lower coefficient. -/
theorem GaussParameters.pochhammer_ne_zero_of_le (c : K) {k n : ℕ}
    (hc : (ascPochhammer K k).eval c ≠ 0) (hn : n ≤ k) :
    (ascPochhammer K n).eval c ≠ 0 := by
  have hp := congrArg (fun p : K[X] ↦ p.eval c) (ascPochhammer_mul K n (k - n))
  simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast, Nat.add_sub_of_le hn] at hp
  intro hz
  apply hc
  rw [← hp, hz, zero_mul]

variable [CharZero K]

/-- A finite nonzero Pochhammer factor certifies either terminating numerator. -/
def GaussParameters.ofTerminating (a b c : K) (k : ℕ)
    (hk : a = -(k : K) ∨ b = -(k : K))
    (hc : (ascPochhammer K k).eval c ≠ 0) : GaussParameters K :=
  ⟨a, b, c, fun n hn ↦ by
    by_cases hnk : n ≤ k
    · exact False.elim (GaussParameters.pochhammer_ne_zero_of_le c hc hnk hn)
    · have hz : (ascPochhammer K n).eval (-(k : K)) = 0 :=
        (ascPochhammer_eval_eq_zero_iff n (-(k : K))).mpr ⟨k, by omega, by simp⟩
      rcases hk with ha | hb
      · rw [ha, hz, zero_mul]
      · rw [hb, hz, mul_zero]⟩
end Parameters


section QuadraticParameters
variable {K : Type*} [Field K] [CharZero K]
/-- One of the quadratic numerator parameters terminates at the half-degree. -/
theorem GaussParameters.quadratic_terminates (n : ℕ) :
    -(n : K) / 2 = -((n / 2 : ℕ) : K) ∨
      (1 - (n : K)) / 2 = -((n / 2 : ℕ) : K) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left
    have hn : (n : K) = 2 * ((n / 2 : ℕ) : K) := by
      exact_mod_cast (show n = 2 * (n / 2) by omega)
    rw [hn]
    ring
  · right
    have hn : (n : K) = 2 * ((n / 2 : ℕ) : K) + 1 := by
      exact_mod_cast (show n = 2 * (n / 2) + 1 by omega)
    rw [hn]
    ring

/-- Quadratic terminating data require exactly the finite nonzero denominator factors. -/
def GaussParameters.quadratic (n : ℕ) (c : K)
    (hc : (ascPochhammer K (n / 2)).eval c ≠ 0) : GaussParameters K :=
  .ofTerminating (-(n : K) / 2) ((1 - (n : K)) / 2) c (n / 2)
    (quadratic_terminates n) hc

/-- The certified quadratic parameter object has a terminating numerator. -/
theorem GaussParameters.quadratic_has_termination (n : ℕ) (c : K)
    (hc : (ascPochhammer K (n / 2)).eval c ≠ 0) :
    (quadratic n c hc).a = -((n / 2 : ℕ) : K) ∨
      (quadratic n c hc).b = -((n / 2 : ℕ) : K) := quadratic_terminates n

/-- A negative integer denominator is nonzero through its finite admissible range. -/
theorem GaussParameters.pochhammer_neg_nat_ne_zero (m k : ℕ) (hk : k ≤ m) :
    (ascPochhammer K k).eval (-(m : K)) ≠ 0 := by
  intro hz
  obtain ⟨j, hj, he⟩ := (ascPochhammer_eval_eq_zero_iff k (-(m : K))).mp hz
  have hcast : (j : K) = (m : K) := by simpa only [neg_neg] using he
  have hjm : j = m := by exact_mod_cast hcast
  omega
end QuadraticParameters
