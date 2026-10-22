/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Chebyshev.Operators
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Operators
public import LeanFun.Mathlib.Algebra.Polynomial.Sequence

/-! # Concrete Chebyshev and ultraspherical coefficient spaces
Polynomial bases retain the full constant convention. They are distinct from
normalised weighted Hilbert bases. Reference: Olver--Townsend (2013), Sections 2--3.
-/

public section
namespace Polynomial
open Module

/-- The canonical real Chebyshev polynomial basis, reusing Mathlib's sequence. -/
@[expose] noncomputable def chebyshevBasis : Basis ℕ ℝ ℝ[X] :=
  (Chebyshev.chebyshevTsequence ℝ).basis (Chebyshev.chebyshevTsequence ℝ).isUnit_leadingCoeff

@[simp] theorem chebyshevBasis_apply (n : ℕ) : chebyshevBasis n = Chebyshev.T ℝ n := by
  simp [chebyshevBasis, Sequence.basis_eq_self, Chebyshev.chebyshevTsequence]

/-- The real Chebyshev-to-`C^(1)` matrix has bandwidths `(0,2)`. -/
theorem chebyshevBasis_conversion_isBanded :
    ((gegenbauerBasis (by norm_num : -(1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) ≠ 0)).toMatrix
      chebyshevBasis).IsBanded 0 2 := by
  rw [show (chebyshevBasis : ℕ → ℝ[X]) = (fun j : ℕ ↦ Chebyshev.T ℝ j) from
    by funext j; exact chebyshevBasis_apply j]
  apply chebyshev_gegenbauer_conversion_isBanded
  exact gegenbauerBasis_apply _ _

/-- Every positive-order derivative enters its concrete ultraspherical basis
with a single upper diagonal (Olver--Townsend, Section 3). -/
theorem chebyshevBasis_iterate_derivative_isBanded (k : ℕ) :
    ((gegenbauerBasis (by linarith [Nat.cast_nonneg (α := ℝ) k] : -(1 / 2 : ℝ) < (k : ℝ) + 1)
      (by positivity : (k : ℝ) + 1 ≠ 0)).toMatrix
        (fun j ↦ derivative^[k + 1] (chebyshevBasis j))).IsBanded 0 (k + 1) := by
  simp only [chebyshevBasis_apply]
  apply chebyshev_iterate_derivative_isBanded
  exact gegenbauerBasis_apply _ _

end Polynomial
