/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Map

/-!
# Jacobi connection numerators and denominators

Polynomial expressions for the one-parameter connection formula. The denominator
has the removable alpha+beta+1 factor cancelled, so the orthogonality range has
no exceptional parameters. Reference: DLMF 18.18.14.
-/

public section
namespace Polynomial
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Numerator of the degree `k` coefficient of `P_n^(γ,β)` in the `(α,β)` family
(DLMF 18.18.14). -/
@[expose] noncomputable def jacobiAlphaConnectionNumerator (α β γ : R) (n k : ℕ) : R :=
  (ascPochhammer R (n - k)).eval (β + k + 1) *
    (ascPochhammer R k).eval ((n : R) + γ + β + 1) *
    (ascPochhammer R (n - k)).eval (γ - α)

/-- Denominator of the one-parameter Jacobi connection coefficient, with its
removable singularity cancelled (DLMF 18.18.14). -/
@[expose] noncomputable def jacobiAlphaConnectionDenominator (α β : R) (n k : ℕ) : R :=
  (ascPochhammer R k).eval ((k : R) + α + β + 1) *
    (ascPochhammer R (n - k)).eval (α + β + 2 * k + 2) * (n - k).factorial

/-- A polynomial common denominator for all degree-at-most-`n` coefficients. -/
@[expose] noncomputable def jacobiAlphaConnectionScale (α β : R) (n : ℕ) : R :=
  ∏ j : Fin (n + 1), jacobiAlphaConnectionDenominator α β n j

/-- The cleared coefficient multiplies its numerator by every other denominator. -/
@[expose] noncomputable def jacobiAlphaConnectionCleared (α β γ : R) (n : ℕ)
    (k : Fin (n + 1)) : R :=
  jacobiAlphaConnectionNumerator α β γ n k *
    ∏ j ∈ Finset.univ.erase k, jacobiAlphaConnectionDenominator α β n j

/-- Connection numerators commute with ring homomorphisms. -/
@[simp] theorem map_jacobiAlphaConnectionNumerator (f : R →+* S) (α β γ : R) (n k : ℕ) :
    f (jacobiAlphaConnectionNumerator α β γ n k) =
      jacobiAlphaConnectionNumerator (f α) (f β) (f γ) n k := by
  have hp (j : ℕ) (x : R) : f ((ascPochhammer R j).eval x) =
      (ascPochhammer S j).eval (f x) := by
    rw [← ascPochhammer_map f, eval_map]
    exact (eval₂_at_apply f x).symm
  simp only [jacobiAlphaConnectionNumerator, map_mul, hp, map_add, map_natCast, map_one, map_sub]

/-- Connection denominators commute with ring homomorphisms. -/
@[simp] theorem map_jacobiAlphaConnectionDenominator (f : R →+* S) (α β : R) (n k : ℕ) :
    f (jacobiAlphaConnectionDenominator α β n k) =
      jacobiAlphaConnectionDenominator (f α) (f β) n k := by
  have hp (j : ℕ) (x : R) : f ((ascPochhammer R j).eval x) =
      (ascPochhammer S j).eval (f x) := by
    rw [← ascPochhammer_map f, eval_map]
    exact (eval₂_at_apply f x).symm
  simp only [jacobiAlphaConnectionDenominator, map_mul, hp, map_add, map_natCast,
    map_one, map_ofNat]

/-- The common connection denominator commutes with ring homomorphisms. -/
@[simp] theorem map_jacobiAlphaConnectionScale (f : R →+* S) (α β : R) (n : ℕ) :
    f (jacobiAlphaConnectionScale α β n) = jacobiAlphaConnectionScale (f α) (f β) n := by
  simp [jacobiAlphaConnectionScale]

/-- Cleared connection coefficients commute with ring homomorphisms. -/
@[simp] theorem map_jacobiAlphaConnectionCleared (f : R →+* S) (α β γ : R) (n : ℕ)
    (k : Fin (n + 1)) :
    f (jacobiAlphaConnectionCleared α β γ n k) =
      jacobiAlphaConnectionCleared (f α) (f β) (f γ) n k := by
  simp [jacobiAlphaConnectionCleared]

end Polynomial
