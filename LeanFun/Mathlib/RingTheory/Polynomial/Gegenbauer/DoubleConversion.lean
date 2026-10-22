/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.Conversion
import Mathlib.Tactic.LinearCombination

/-!
# Two successive Gegenbauer parameter raisings

The three coefficients have signs positive, negative, positive when the
parameter is positive. These signs control the maximal inner-index steps of
Cartesian disk multiplication by y². Reference: DLMF 18.9.7.
-/

public section
namespace Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Two parameter raisings with all denominators cleared. -/
theorem gegenbauer_double_conversion (lam : R) (n : ℕ) :
    C (((n : R)+lam+4)*((n : R)+lam+5)*((n : R)+lam+3)) *
        gegenbauer lam (n+4) =
      C (lam*(lam+1)*((n : R)+lam+3)) * gegenbauer (lam+2) (n+4) -
      C (2*lam*(lam+1)*((n : R)+lam+4)) * gegenbauer (lam+2) (n+2) +
      C (lam*(lam+1)*((n : R)+lam+5)) * gegenbauer (lam+2) n := by
  have h₀ := gegenbauer_conversion lam (n+2)
  have h₁ := gegenbauer_conversion (lam+1) (n+2)
  have h₂ := gegenbauer_conversion (lam+1) n
  have he : lam+1+1 = lam+2 := by ring
  simp only [Nat.cast_add, Nat.cast_ofNat, he] at h₀ h₁ h₂
  change C (((n : R)+lam+4)*((n : R)+lam+5)*((n : R)+lam+3)) *
      gegenbauer lam (n+2+2) = _
  simp only [map_mul, map_add, map_natCast, map_ofNat, map_one] at h₀ h₁ h₂ ⊢
  linear_combination
    (((n : R[X])+C lam+5)*((n : R[X])+C lam+3))*h₀ +
    C lam*((n : R[X])+C lam+3)*h₁ -
    C lam*((n : R[X])+C lam+5)*h₂

/-- Degree two has only the top and middle terms of the double conversion. -/
theorem gegenbauer_double_conversion_two (lam : R) :
    C ((lam+2)*(lam+3))*gegenbauer lam 2 =
      C (lam*(lam+1))*gegenbauer (lam+2) 2 - C (2*lam*(lam+2)) := by
  have h₀ := gegenbauer_conversion lam 0
  have h₁ := gegenbauer_conversion (lam+1) 0
  have he : lam+1+1=lam+2 := by ring
  simp only [Nat.cast_zero, zero_add, he, gegenbauer_zero,
    map_mul, map_add, map_ofNat, map_one] at h₀ h₁ ⊢
  linear_combination (C lam+3)*h₀+C lam*h₁

/-- Degree three has only the top and middle terms of the double conversion. -/
theorem gegenbauer_double_conversion_three (lam : R) :
    C ((lam+3)*(lam+4)*(lam+2))*gegenbauer lam 3 =
      C (lam*(lam+1)*(lam+2))*gegenbauer (lam+2) 3 -
      C (2*lam*(lam+1)*(lam+3))*gegenbauer (lam+2) 1 := by
  have h₀ := gegenbauer_conversion lam 1
  have h₁ := gegenbauer_conversion (lam+1) 1
  have h₂ := gegenbauer_conversion_one (lam+1)
  have he : lam+1+1=lam+2 := by ring
  simp only [Nat.cast_one, he, map_mul, map_add, map_ofNat, map_one] at h₀ h₁ h₂ ⊢
  linear_combination
    (C lam+4)*(C lam+2)*h₀+C lam*(C lam+2)*h₁-C lam*(C lam+4)*h₂

end Polynomial
