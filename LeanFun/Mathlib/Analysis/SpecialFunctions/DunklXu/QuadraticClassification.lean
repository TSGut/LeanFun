/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticUniformNecessity
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.UniformSeparated
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.QuadraticFactors
import Mathlib.Tactic.Ring

/-! # Classification of uniform quadratic Cartesian sparsity
For nonzero nonnegative diagonal quadratics, canonical factors have uniformly
finite inner bandwidth over all admissible factor measures exactly in the two
separated cases. Reference: Cartesian separation and the all-degree obstruction.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

private theorem quadratic_nonneg_interval (A B : ℝ) (hA : 0 ≤ A) (hAB : 0 ≤ A + B)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ (Polynomial.C A + Polynomial.C B * Polynomial.X ^ 2).eval x := by
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  nlinarith [mul_nonneg hA (sub_nonneg.mpr hx2), mul_nonneg hAB (sq_nonneg x)]

private theorem quadratic_degree_le (A B : ℝ) :
    (Polynomial.C A + Polynomial.C B * Polynomial.X ^ 2).natDegree ≤ 2 := by
  apply (natDegree_add_le _ _).trans
  apply max_le (by simp)
  exact (natDegree_mul_le).trans (by simp)

private theorem quadratic_coeff_even (A B : ℝ) (i : ℕ) (hi : i % 2 ≠ 0) :
    (Polynomial.C A + Polynomial.C B * Polynomial.X ^ 2).coeff i = 0 := by
  have h0 : i ≠ 0 := by omega
  have h2 : i ≠ 2 := by omega
  simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, h0, h2]

/-- Both separated quadratic cases have uniform canonical inner bandwidth. -/
theorem hasUniformCartesianInnerBandwidth_coordinateQuadratic_of_separated (A B C : ℝ)
    (hu0 : coordinateQuadratic A B C ≠ 0)
    (hA : 0 ≤ A) (hAB : 0 ≤ A + B) (hAC : 0 ≤ A + C) (hsep : C * (A + B) = 0) :
    HasUniformCartesianInnerBandwidth (coordinateQuadratic A B C) := by
  rcases mul_eq_zero.mp hsep with hC | hAB0
  · subst C
    have hq : (Polynomial.C A + Polynomial.C B * Polynomial.X ^ 2 : ℝ[X]) ≠ 0 := by
      intro hz
      apply hu0
      rw [coordinateQuadratic_outer, hz]
      simp [cartesianDiskModification, cartesianDiskPolynomial]
    rw [coordinateQuadratic_outer]
    apply hasUniformCartesianInnerBandwidth_separated _ 1 0 hq one_ne_zero
      (quadratic_nonneg_interval A B hA hAB)
    · simp
    · simp
    · intro i hi
      have : i ≠ 0 := by omega
      change (1 : ℝ[X]).coeff i = 0
      simp [Polynomial.coeff_one, this]
    · simp
  · have hB : B = -A := by linarith
    subst B
    have hq : (Polynomial.C A + Polynomial.C C * Polynomial.X ^ 2 : ℝ[X]) ≠ 0 := by
      intro hz
      apply hu0
      rw [coordinateQuadratic_radius, hz]
      simp [cartesianDiskModification, cartesianDiskPolynomial, diskLift]
    rw [coordinateQuadratic_radius]
    apply hasUniformCartesianInnerBandwidth_separated 1 _ 1 one_ne_zero hq
    · simp
    · exact quadratic_nonneg_interval A C hA hAC
    · intro x
      simp
    · exact quadratic_coeff_even A C
    · simpa using quadratic_degree_le A C

/-- Uniform finite inner bandwidth is equivalent to Cartesian quadratic separation.
The bandwidth is chosen before the measures and before every degree section. -/
theorem hasUniformCartesianInnerBandwidth_coordinateQuadratic_iff (A B C : ℝ)
    (hu0 : coordinateQuadratic A B C ≠ 0)
    (hA : 0 ≤ A) (hAB : 0 ≤ A + B) (hAC : 0 ≤ A + C) :
    HasUniformCartesianInnerBandwidth (coordinateQuadratic A B C) ↔ C * (A + B) = 0 :=
  ⟨coordinateQuadratic_separated_of_uniform_inner_bandwidth A B C hA hAB hAC,
    hasUniformCartesianInnerBandwidth_coordinateQuadratic_of_separated A B C hu0 hA hAB hAC⟩

end MvPolynomial
