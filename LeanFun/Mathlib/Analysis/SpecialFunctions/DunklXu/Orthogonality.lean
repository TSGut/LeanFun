/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Pairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.DiskOuterMeasure
import Mathlib.Tactic.Ring

/-!
# Orthogonality of Cartesian Dunkl–Xu polynomials

Inner-index orthogonality is Jacobi orthogonality in the vertical parameter.
For equal inner indices, the square of the lift raises the outer Jacobi weight.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, disk families.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- Different inner indices are orthogonal independently of the outer indices. -/
theorem integral_mul_dunklXuDisk_eq_zero_of_inner_ne {β : ℝ} (hβ : -1 < β)
    (n k m j : ℕ) (hkj : k ≠ j) :
    ∫ v, eval v (dunklXuDisk β n k) * eval v (dunklXuDisk β m j)
      ∂dunklXuDiskMeasure β = 0 := by
  have hα : -1 < β+1/2 := by linarith
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isFiniteMeasure_jacobiMeasure hα hα
  have he := integralInner_cartesianDiskPolynomial
    (μ := jacobiMeasure (β+1/2) (β+1/2)) (ν := jacobiMeasure β β)
    (ae_mem_Icc_jacobiMeasure _ _)
    (jacobi (β+k+1/2) (β+k+1/2) (n-k))
    (jacobi (β+j+1/2) (β+j+1/2) (m-j))
    (jacobi β β k) (jacobi β β j) k j
    (natDegree_jacobi_le _ _ _) (natDegree_jacobi_le _ _ _)
    (coeff_jacobi_symmetric_eq_zero_of_parity β k)
    (coeff_jacobi_symmetric_eq_zero_of_parity β j)
    (ho := (hasFiniteMoments_jacobiMeasure hα hα).integrable_disk_outer_factor
      (ae_mem_Icc_jacobiMeasure _ _) _ _ _)
    (hi := (hasFiniteMoments_jacobiMeasure hβ hβ).integrable_mul _ _)
  rw [Polynomial.integralInner, integral_mul_jacobi_eq_zero hβ hβ hkj, mul_zero] at he
  simpa only [integralInner, cartesianDiskPolynomial, dunklXuDisk, dunklXuDiskMeasure] using he

/-- Equal inner indices leave a shifted outer Jacobi pairing. -/
theorem integral_mul_dunklXuDisk_same_inner {β : ℝ} (hβ : -1 < β) (n m k : ℕ) :
    (∫ v, eval v (dunklXuDisk β n k) * eval v (dunklXuDisk β m k)
      ∂dunklXuDiskMeasure β) =
    (∫ x, (jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)).eval x *
      (jacobi (β + k + 1 / 2) (β + k + 1 / 2) (m - k)).eval x
      ∂jacobiMeasure (β + k + 1 / 2) (β + k + 1 / 2)) *
    (∫ z, (jacobi β β k).eval z ^ 2 ∂jacobiMeasure β β) := by
  have hα : -1 < β+1/2 := by linarith
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isFiniteMeasure_jacobiMeasure hα hα
  have he := integralInner_cartesianDiskPolynomial_same_degree
    (μ := jacobiMeasure (β+1/2) (β+1/2)) (ν := jacobiMeasure β β)
    (ae_mem_Icc_jacobiMeasure _ _)
    (jacobi (β+k+1/2) (β+k+1/2) (n-k))
    (jacobi (β+k+1/2) (β+k+1/2) (m-k))
    (jacobi β β k) (jacobi β β k) k
    (natDegree_jacobi_le _ _ _) (natDegree_jacobi_le _ _ _)
    (coeff_jacobi_symmetric_eq_zero_of_parity β k)
    (coeff_jacobi_symmetric_eq_zero_of_parity β k)
    (ho := ((hasFiniteMoments_jacobiMeasure hα hα).diskOuterMeasure
      (ae_mem_Icc_jacobiMeasure _ _) k).integrable_mul _ _)
    (hi := (hasFiniteMoments_jacobiMeasure hβ hβ).integrable_mul _ _)
  simp only [integralInner, Polynomial.integralInner] at he
  have hshift : -1 < (β+1/2)+(k : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have htarget := (hasFiniteMoments_jacobiMeasure hshift hshift).integrable_mul
    (jacobi (β+k+1/2) (β+k+1/2) (n-k))
    (jacobi (β+k+1/2) (β+k+1/2) (m-k))
  have hs := (integral_jacobiMeasure_add_nat_integrable (β+1/2) (β+1/2) k
    ⟨_, htarget⟩).2
  have ho := ((hasFiniteMoments_jacobiMeasure hα hα).diskOuterMeasure
    (ae_mem_Icc_jacobiMeasure _ _) k).integrable_mul
      (jacobi (β+k+1/2) (β+k+1/2) (n-k))
      (jacobi (β+k+1/2) (β+k+1/2) (m-k))
  have ht := integral_diskOuterMeasure (jacobiMeasure (β+1/2) (β+1/2))
    (ae_mem_Icc_jacobiMeasure _ _) k ⟨_, ho⟩
  dsimp only at hs ht
  rw [ht, ← hs] at he
  simpa only [cartesianDiskPolynomial, dunklXuDisk, dunklXuDiskMeasure,
    show β+1/2+(k:ℝ) = β+k+1/2 by ring, ← sq] using he

/-- Distinct valid disk indices are orthogonal. -/
theorem integral_mul_dunklXuDisk_eq_zero {β : ℝ} (hβ : -1 < β)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m) (hne : (n, k) ≠ (m, j)) :
    ∫ v, eval v (dunklXuDisk β n k) * eval v (dunklXuDisk β m j)
      ∂dunklXuDiskMeasure β = 0 := by
  by_cases hkj : k = j
  · subst j
    rw [integral_mul_dunklXuDisk_same_inner hβ,
      integral_mul_jacobi_eq_zero
        (show -1 < β + k + 1 / 2 by have := Nat.cast_nonneg (α := ℝ) k; linarith)
        (show -1 < β + k + 1 / 2 by have := Nat.cast_nonneg (α := ℝ) k; linarith)
        (show n - k ≠ m - k by intro h; apply hne; congr 1; omega), zero_mul]
  · exact integral_mul_dunklXuDisk_eq_zero_of_inner_ne hβ n k m j hkj

/-- The squared norm is the product of the standard inner and outer Jacobi norms. -/
theorem integral_sq_dunklXuDisk {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    (∫ v, eval v (dunklXuDisk β n k) ^ 2 ∂dunklXuDiskMeasure β) =
    (∫ x, (jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)).eval x ^ 2
      ∂jacobiMeasure (β + k + 1 / 2) (β + k + 1 / 2)) *
    (∫ z, (jacobi β β k).eval z ^ 2 ∂jacobiMeasure β β) := by
  simpa only [sq] using integral_mul_dunklXuDisk_same_inner hβ n n k

/-- Every member has a strictly positive squared norm in the orthogonality range. -/
theorem integral_sq_dunklXuDisk_pos {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    0 < ∫ v, eval v (dunklXuDisk β n k) ^ 2 ∂dunklXuDiskMeasure β := by
  rw [integral_sq_dunklXuDisk hβ]
  have ha : -1 < β + k + 1 / 2 := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  apply mul_pos
  · exact hasPositiveDefiniteIntegral_jacobiMeasure ha ha _
      (fun h => (coeff_jacobi_self_pos ha ha (n - k)).ne' (by rw [h]; simp))
  · exact hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ _
      (fun h => (coeff_jacobi_self_pos hβ hβ k).ne' (by rw [h]; simp))

end MvPolynomial
