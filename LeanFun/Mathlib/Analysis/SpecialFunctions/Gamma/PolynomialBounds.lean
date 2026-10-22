/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Elementary polynomial bounds for shifted Gamma functions

Monotonicity of Gamma on [2,infinity) compares real shifts with integer shifts.
These bounds are deliberately nonsharp and are useful for spectral convergence.
References: DLMF 5.5.1 and 5.6; the Bohr--Mollerup theorem.
-/

public section
namespace Real
open _root_.Polynomial Set

/-- Gamma at a positive real argument shifted by a natural number. -/
private theorem Gamma_add_nat_eq_ascPochhammer_mul_raw {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Gamma (a + n) = (ascPochhammer ℝ n).eval a * Gamma a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
      Gamma_add_one (by positivity : a + (n : ℝ) ≠ 0), ih, ascPochhammer_succ_eval]
    ring

/-- Comparing a real shift with an integer shift bounds Gamma by a factorial
and a fixed-degree polynomial in the index. -/
private theorem Gamma_nat_add_le_factorial_mul_pow_raw (n k : ℕ) {a : ℝ}
    (ha : a ≤ k + 1) (hna : 2 ≤ (n : ℝ) + a) :
    Gamma ((n : ℝ) + a) ≤ n.factorial * ((n : ℝ) + k) ^ k := by
  have hupper : (n : ℝ) + a ≤ (n + k : ℕ) + 1 := by exact_mod_cast (by linarith :
    (n : ℝ) + a ≤ (n : ℝ) + (k : ℝ) + 1)
  have hg := Gamma_strictMonoOn_Ici.monotoneOn hna (hna.trans hupper) hupper
  rw [Gamma_nat_eq_factorial] at hg
  apply hg.trans
  rw [← Nat.factorial_mul_ascFactorial, Nat.cast_mul]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.ascFactorial_le_pow_add n k

/-- Shifts by at least one give a factorial lower bound once n is positive. -/
private theorem factorial_le_Gamma_nat_add_raw {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 1 ≤ a) :
    (n.factorial : ℝ) ≤ Gamma ((n : ℝ) + a) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlow : (2 : ℝ) ≤ n + 1 := by linarith
  have hle : (n : ℝ) + 1 ≤ n + a := by linarith
  simpa only [Gamma_nat_eq_factorial] using
    Gamma_strictMonoOn_Ici.monotoneOn hlow (hlow.trans hle) hle

/-- A positive rising-factorial ratio grows at most polynomially. The exponent
is any integer above a-1; constants are deliberately nonsharp. -/
private theorem ascPochhammer_div_factorial_le_polynomial_raw {a : ℝ} (ha : 0 < a)
    (k : ℕ) (hk : a ≤ k + 1) (n : ℕ) :
    (ascPochhammer ℝ n).eval a / (n.factorial : ℝ) ≤
      (1 + |a| + ((k : ℝ) + 1) ^ k / Gamma a) * ((n : ℝ) + 1) ^ k := by
  let C : ℝ := 1 + |a| + ((k : ℝ) + 1) ^ k / Gamma a
  have hg : 0 < Gamma a := Gamma_pos_of_pos ha
  have hpow : 0 ≤ ((k : ℝ) + 1) ^ k / Gamma a := by positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg a]
  have hCa : a ≤ C := by dsimp [C]; linarith [le_abs_self a]
  have hCpow : ((k : ℝ) + 1) ^ k / Gamma a ≤ C := by
    dsimp [C]
    linarith [abs_nonneg a]
  change _ ≤ C * ((n : ℝ) + 1) ^ k
  rcases n with _ | n
  · simpa using hC1
  rcases n with _ | n
  · simp only [Nat.zero_add, ascPochhammer_one, eval_X, Nat.factorial_one,
      Nat.cast_one, div_one]
    exact hCa.trans (le_mul_of_one_le_right hC (one_le_pow₀ (by norm_num)))
  have hn : (2 : ℝ) ≤ (n + 1 + 1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ n + 1 + 1)
  have hb := Gamma_nat_add_le_factorial_mul_pow_raw (n + 1 + 1) k hk (by linarith)
  rw [add_comm, Gamma_add_nat_eq_ascPochhammer_mul_raw ha] at hb
  have hf : (0 : ℝ) < (n + 1 + 1).factorial := by positivity
  have hr : (ascPochhammer ℝ (n + 1 + 1)).eval a / ((n + 1 + 1).factorial : ℝ) ≤
      (((n + 1 + 1 : ℕ) : ℝ) + k) ^ k / Gamma a := by
    apply (div_le_div_iff₀ hf hg).mpr
    simpa only [mul_comm] using hb
  apply hr.trans
  calc
    _ ≤ ((((k : ℝ) + 1) * (((n + 1 + 1 : ℕ) : ℝ) + 1)) ^ k) / Gamma a := by
      apply div_le_div_of_nonneg_right _ hg.le
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    _ = (((k : ℝ) + 1) ^ k / Gamma a) * (((n + 1 + 1 : ℕ) : ℝ) + 1) ^ k := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hCpow (by positivity)

/-- Gamma at a positive argument shifted by a natural number, within its domain. -/
theorem Gamma_add_nat_eq_ascPochhammer_mul {a : ℝ} (ha : 0 < a) (n : ℕ) :
    GammaOn (GammaPoint.ofPos (a + n) (by positivity)) =
      (ascPochhammer ℝ n).eval a * GammaOn (GammaPoint.ofPos a ha) :=
  Gamma_add_nat_eq_ascPochhammer_mul_raw ha n

/-- A factorial upper bound for a genuine Gamma value. -/
theorem Gamma_nat_add_le_factorial_mul_pow (n k : ℕ) {a : ℝ}
    (ha : a ≤ k + 1) (hna : 2 ≤ (n : ℝ) + a) :
    GammaOn (GammaPoint.ofPos ((n : ℝ) + a) (by linarith)) ≤
      n.factorial * ((n : ℝ) + k) ^ k :=
  Gamma_nat_add_le_factorial_mul_pow_raw n k ha hna

/-- A factorial lower bound for a genuine Gamma value. -/
theorem factorial_le_Gamma_nat_add {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 1 ≤ a) :
    (n.factorial : ℝ) ≤ GammaOn (GammaPoint.ofPos ((n : ℝ) + a)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)) :=
  factorial_le_Gamma_nat_add_raw hn ha

/-- A positive rising-factorial ratio has polynomial growth with a classical constant. -/
theorem ascPochhammer_div_factorial_le_polynomial {a : ℝ} (ha : 0 < a)
    (k : ℕ) (hk : a ≤ k + 1) (n : ℕ) :
    (ascPochhammer ℝ n).eval a / (n.factorial : ℝ) ≤
      (1 + |a| + ((k : ℝ) + 1) ^ k / GammaOn (GammaPoint.ofPos a ha)) *
        ((n : ℝ) + 1) ^ k :=
  ascPochhammer_div_factorial_le_polynomial_raw ha k hk n

end Real
