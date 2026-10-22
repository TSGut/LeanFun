/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticSigns
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.EvenMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionSupport

/-! # Inner bandwidth and parity of quadratic disk multiplication
Outer-coordinate multiplication preserves the inner index. Multiplication by y²
has inner bandwidth two and preserves inner parity.
Reference: Dunkl--Xu, Cartesian disk construction.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- Any polynomial in the first coordinate preserves the inner index. -/
theorem integralInner_outer_mul_dunklXuDisk_eq_zero {β : ℝ} (hβ : -1 < β)
    (p : ℝ[X]) (n k m j : ℕ) (hkj : k ≠ j) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (p.eval₂ C (X 0) * dunklXuDisk β n k) (dunklXuDisk β m j)) = 0 := by
  have hα : -1 < β+1/2 := by linarith
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isFiniteMeasure_jacobiMeasure hα hα
  have he := integralInner_cartesianDiskPolynomial
    (μ := jacobiMeasure (β+1/2) (β+1/2)) (ν := jacobiMeasure β β)
    (ae_mem_Icc_jacobiMeasure _ _)
    (p*jacobi (β+k+1/2) (β+k+1/2) (n-k))
    (jacobi (β+j+1/2) (β+j+1/2) (m-j))
    (jacobi β β k) (jacobi β β j) k j
    (natDegree_jacobi_le _ _ _) (natDegree_jacobi_le _ _ _)
    (coeff_jacobi_symmetric_eq_zero_of_parity β k)
    (coeff_jacobi_symmetric_eq_zero_of_parity β j)
    (ho := (hasFiniteMoments_jacobiMeasure hα hα).integrable_disk_outer_factor
      (ae_mem_Icc_jacobiMeasure _ _) _ _ _)
    (hi := (hasFiniteMoments_jacobiMeasure hβ hβ).integrable_mul _ _)
  rw [Polynomial.integralInner, integral_mul_jacobi_eq_zero hβ hβ hkj, mul_zero] at he
  simpa only [integralInner, cartesianDiskPolynomial, dunklXuDisk, dunklXuDiskMeasure,
    Polynomial.eval₂_mul, map_mul, mul_assoc] using he

/-- No upward inner step larger than two occurs in multiplication by y². -/
theorem integralInner_y_sq_dunklXuDisk_eq_zero_of_inner_gap {β : ℝ} (hβ : -1 < β)
    (n k m j : ℕ) (hkj : k + 2 < j) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (X 1 ^ 2 * dunklXuDisk β n k) (dunklXuDisk β m j)) = 0 := by
  rw [integralInner_y_sq_dunklXuDisk_separated hβ]
  have hz := (isOrthogonal_jacobiSequence hβ hβ).integralInner_eq_zero_of_degree_lt
    (hasFiniteMoments_jacobiMeasure hβ hβ) (p := Polynomial.X ^ 2 * jacobi β β k) (n := j)
  have hd : (Polynomial.X ^ 2 * jacobi β β k).degree < (j : WithBot ℕ) := by
    calc
      _ = ((k + 2 : ℕ) : WithBot ℕ) := by
        rw [degree_mul, degree_pow, degree_X, degree_jacobi_of_neg_one_lt hβ hβ]
        push_cast
        ring
      _ < j := by exact_mod_cast hkj
  rw [show Polynomial.integralInner (jacobiMeasure β β) (Polynomial.IntegrablePair.of (jacobiMeasure β β) (Polynomial.X ^ 2 * jacobi β β k) (jacobi β β j)) = 0 from hz hd, mul_zero]

/-- Inner parity is preserved exactly, independently of total degrees. -/
theorem integralInner_y_sq_dunklXuDisk_eq_zero_of_inner_parity {β : ℝ} (hβ : -1 < β)
    (n k m j : ℕ) (hkj : k % 2 ≠ j % 2) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (X 1 ^ 2 * dunklXuDisk β n k) (dunklXuDisk β m j)) = 0 := by
  let := isNegInvariant_jacobiMeasure β
  rw [integralInner_y_sq_dunklXuDisk_separated hβ]
  have hk := comp_neg_X_eq_of_coeff_parity k (coeff_jacobi_symmetric_eq_zero_of_parity β k)
  have hj := comp_neg_X_eq_of_coeff_parity j (coeff_jacobi_symmetric_eq_zero_of_parity β j)
  have hp : (Polynomial.X ^ 2 * jacobi β β k).comp (-Polynomial.X) =
      Polynomial.C ((-1 : ℝ) ^ k) * (Polynomial.X ^ 2 * jacobi β β k) := by
    simp only [mul_comp, pow_comp, X_comp, neg_sq, hk]
    ring
  rw [integralInner_eq_zero_of_opposite_parity hp hj hkj, mul_zero]

end MvPolynomial
