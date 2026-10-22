/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Polynomial.FiniteClenshaw
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Recurrence

import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Clenshaw evaluation of Gegenbauer expansions

Only positive natural numbers are divided by. The parameter is unrestricted,
including the degenerate case `lam = 0`. References: Clenshaw (1955);
DLMF Table 18.9.1 and §18.40(i).
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Nonzero denominators at exactly the recurrence indices used by an expansion. -/
def GegenbauerClenshawInput (K : Type*) [Field K] (n : ℕ) : Prop :=
  ∀ i : Fin (n - 2), (i.val : K) + 2 ≠ 0

/-- Rational algebras over fields admit every finite Gegenbauer recurrence. -/
theorem GegenbauerClenshawInput.ofRatAlgebra (n : ℕ) :
    GegenbauerClenshawInput K n := by
  let : CharZero K := Algebra.charZero_of_charZero ℚ K
  intro i
  exact_mod_cast (show i.val + 2 ≠ 0 by omega)

/-- Executable evaluation with finite denominator certificates (DLMF Table 18.9.1). -/
def clenshawGegenbauer (lam x : K) (c : ℕ → K) (n : ℕ)
    (_d : GegenbauerClenshawInput K n :=
      by exact Polynomial.GegenbauerClenshawInput.ofRatAlgebra _) : K :=
  finiteClenshaw n (fun k ↦ 2 * (k.val + lam + 1) * x / (k.val + 2))
    (fun k ↦ -(k.val + 2 * lam) / (k.val + 2)) (fun i ↦ c i.val) 1 (2 * lam * x)

/-- Clenshaw evaluation is exact for every Gegenbauer parameter. -/
theorem clenshawGegenbauer_eq_sum (lam x : K) (c : ℕ → K) (n : ℕ) :
    clenshawGegenbauer lam x c n =
      ∑ i ∈ Finset.range n, c i * (gegenbauer lam i).eval x := by
  let : CharZero K := Algebra.charZero_of_charZero ℚ K
  have hp (k : ℕ) : (gegenbauer lam (k + 2)).eval x =
      (2 * (k + lam + 1) * x / (k + 2)) * (gegenbauer lam (k + 1)).eval x +
        (-(k + 2 * lam) / (k + 2)) * (gegenbauer lam k).eval x := by
    have hd : (k : K) + 2 ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
    have h := congrArg (fun p : K[X] ↦ p.eval x) (gegenbauer_recurrence lam k)
    simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_zero] at h
    field_simp [hd]
    linear_combination h
  have he := clenshaw_eq_sum _ _ c (fun k ↦ (gegenbauer lam k).eval x) hp n
  have hf := finiteClenshaw_eq
    (fun k ↦ 2 * (k + lam + 1) * x / (k + 2))
    (fun k ↦ -(k + 2 * lam) / (k + 2)) c 1 (2 * lam * x) n
  simpa [clenshawGegenbauer] using hf.trans (by simpa using he)

end Polynomial
