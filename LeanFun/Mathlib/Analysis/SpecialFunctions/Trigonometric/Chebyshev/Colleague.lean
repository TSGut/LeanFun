/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Basic.Complex.Basic
public import LeanFun.Mathlib.Algebra.Polynomial.Sequence.Comrade
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Operators

/-! # Chebyshev colleague matrices
Multiplication modulo the input polynomial uses the full constant coefficient.
Reference: ATAP, Chapter 18.
-/

@[expose] public section
namespace Polynomial.Chebyshev

/-- The colleague matrix of a nonzero real polynomial, after monic scaling.
The zero polynomial is excluded by the characteristic-polynomial theorem. -/
noncomputable def colleagueMatrix (p : ℝ[X]) (hp : p ≠ 0) :
    Matrix (Fin (p * Polynomial.C p.leadingCoeff⁻¹).natDegree)
      (Fin (p * Polynomial.C p.leadingCoeff⁻¹).natDegree) ℝ :=
  (chebyshevTsequence ℝ).comradeMatrix (monic_mul_leadingCoeff_inv hp)

/-- The colleague characteristic polynomial is the input made monic. -/
theorem charpoly_colleagueMatrix (p : ℝ[X]) (hp : p ≠ 0) :
    (colleagueMatrix p hp).charpoly = p * Polynomial.C p.leadingCoeff⁻¹ :=
  (chebyshevTsequence ℝ).charpoly_comradeMatrix (monic_mul_leadingCoeff_inv hp)

/-- Colleague eigenvalues in the base field are exactly the input roots. -/
theorem mem_spectrum_colleagueMatrix_iff (p : ℝ[X]) (hp : p ≠ 0) (x : ℝ) :
    x ∈ spectrum ℝ (colleagueMatrix p hp) ↔ p.IsRoot x := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_colleagueMatrix]
  simp [IsRoot, eval_mul, leadingCoeff_ne_zero.mpr hp]

/-- The colleague dimension is exactly the degree of the input. -/
theorem colleagueMatrix_size (p : ℝ[X]) (hp : p ≠ 0) :
    (p * Polynomial.C p.leadingCoeff⁻¹).natDegree = p.natDegree := by
  simp [hp, natDegree_mul, leadingCoeff_ne_zero.mpr hp]

/-- Explicit entries preserve the full-constant Chebyshev coordinates and
subtract a correction supported in the final column. -/
theorem colleagueMatrix_entry (p : ℝ[X]) (hp : p ≠ 0)
    (i j : Fin (p * Polynomial.C p.leadingCoeff⁻¹).natDegree) :
    colleagueMatrix p hp i j =
      chebyshevBasis.repr (X * T ℝ (j : ℕ)) i -
        (X * T ℝ (j : ℕ)).coeff (p * Polynomial.C p.leadingCoeff⁻¹).natDegree *
          chebyshevBasis.repr (p * Polynomial.C p.leadingCoeff⁻¹) i :=
  (chebyshevTsequence ℝ).comradeMatrix_rank_one_entry (monic_mul_leadingCoeff_inv hp) i j

/-- Complex eigenvalues of the real colleague matrix recover all complex roots. -/
theorem mem_complex_spectrum_colleagueMatrix_iff (p : ℝ[X]) (hp : p ≠ 0) (z : ℂ) :
    z ∈ spectrum ℂ ((colleagueMatrix p hp).map Complex.ofRealHom) ↔
      (p.map Complex.ofRealHom).IsRoot z := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map,
    charpoly_colleagueMatrix, Polynomial.map_mul, Polynomial.map_C]
  simp [IsRoot, eval_mul, leadingCoeff_ne_zero.mpr hp]

end Polynomial.Chebyshev
