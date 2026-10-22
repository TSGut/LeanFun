/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp

/-! # Inverse factorials in rational algebras
Cancellation used by the classical polynomial normalizations (DLMF 18.5).
-/

public section
namespace Nat

/-- Successor cancellation for inverse factorials, mapped to a rational algebra. -/
theorem cast_succ_mul_algebraMap_inv_factorial (R : Type*) [CommRing R] [Algebra ℚ R]
    (n : ℕ) :
    (n + 1 : R) * algebraMap ℚ R (((n + 1).factorial : ℚ)⁻¹) =
      algebraMap ℚ R ((n.factorial : ℚ)⁻¹) := by
  have h : (n + 1 : ℚ) * (((n + 1).factorial : ℚ)⁻¹) = ((n.factorial : ℚ)⁻¹) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  simpa only [map_mul, map_add, map_natCast, map_one] using congrArg (algebraMap ℚ R) h

end Nat
