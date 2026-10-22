/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Polynomial.Clenshaw
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Clenshaw evaluation of Chebyshev expansions

Unlike the half-constant convention in DLMF §3.11(ii), the coefficient `c 0`
is the full constant term. Reference: Clenshaw (1955); DLMF §18.40(i).
-/

@[expose] public section

namespace Polynomial.Chebyshev

variable {R : Type*} [CommRing R]

/-- Executable Clenshaw evaluation of the first `n` Chebyshev coefficients. -/
def clenshawT (c : ℕ → R) (x : R) (n : ℕ) : R :=
  clenshaw (fun _ ↦ 2 * x) (fun _ ↦ -1) c 1 x n

/-- Exact evaluation, with a full (not halved) constant coefficient. -/
theorem clenshawT_eq_sum (c : ℕ → R) (x : R) (n : ℕ) :
    clenshawT c x n = ∑ i ∈ Finset.range n, c i * (T R (i : ℤ)).eval x := by
  have hp (k : ℕ) : (T R ((k + 2 : ℕ) : ℤ)).eval x =
      (2 * x) * (T R ((k + 1 : ℕ) : ℤ)).eval x +
        (-1) * (T R (k : ℤ)).eval x := by
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, T_add_two,
      eval_sub, eval_mul, eval_ofNat, eval_X]
    ring
  simpa [clenshawT] using
    clenshaw_eq_sum (fun _ ↦ 2 * x) (fun _ ↦ -1) c
      (fun k ↦ (T R (k : ℤ)).eval x) hp n

end Polynomial.Chebyshev
