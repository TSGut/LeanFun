/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.ClassicalMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.SymmetricDoubleConnection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.LeadingPairing
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Maximal inner-step pairings for disk multiplication by y²
Separating the Cartesian disk measure identifies the upward inner-index step
with a double symmetric Jacobi conversion. All polynomials retain their original
Jacobi normalization. Reference: Dunkl--Xu, Cartesian disk construction; DLMF 18.9.
-/

public section
open MeasureTheory Set Polynomial
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- Multiplication by y² separates into a radius-weighted outer pairing and
univariate multiplication by the inner coordinate squared. -/
theorem integralInner_y_sq_dunklXuDisk_separated {β : ℝ} (hβ : -1 < β)
    (n k m j : ℕ) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (X 1 ^ 2 * dunklXuDisk β n k) (dunklXuDisk β m j)) =
    (∫ x : Ioo (-1 : ℝ) 1, (jacobiWeight (β + 1 / 2) (β + 1 / 2) x : ℝ) *
      ((jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)).eval (x : ℝ) *
      (jacobi (β + j + 1 / 2) (β + j + 1 / 2) (m - j)).eval (x : ℝ) *
      Real.sqrt (1 - (x : ℝ) ^ 2) ^ (k + j + 2))) *
    Polynomial.integralInner (jacobiMeasure β β) (Polynomial.IntegrablePair.of (jacobiMeasure β β) (Polynomial.X ^ 2 * jacobi β β k) (jacobi β β j)) := by
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isFiniteMeasure_jacobiMeasure
    (show -1 < β + 1 / 2 by linarith) (show -1 < β + 1 / 2 by linarith)
  let : IsFiniteMeasure (volume.withDensity fun x : Ioo (-1 : ℝ) 1 ↦
      (jacobiWeight (β+1/2) (β+1/2) x : ENNReal)) := by
    apply (Measure.isFiniteMeasure_map_iff measurable_subtype_coe.aemeasurable).mp
    change IsFiniteMeasure (jacobiMeasure (β+1/2) (β+1/2))
    infer_instance
  let p : MvPolynomial (Fin 2) ℝ := (X 1 ^ 2 * dunklXuDisk β n k) * dunklXuDisk β m j
  have hi := integral_dunklXuDiskMeasure_open β
    ⟨fun v ↦ eval v p, integrable_dunklXuDiskMeasure hβ p.continuous_eval⟩
  simp only [p, map_mul] at hi
  rw [integralInner]
  simp only [map_mul]
  rw [hi, Polynomial.integralInner]
  have hw := integral_withDensity_eq_integral_smul (μ := volume)
    (jacobiWeight (β + 1/2) (β + 1/2)).continuous.measurable
    (fun x : Ioo (-1 : ℝ) 1 ↦
      (jacobi (β + k + 1/2) (β + k + 1/2) (n-k)).eval (x : ℝ) *
      (jacobi (β + j + 1/2) (β + j + 1/2) (m-j)).eval (x : ℝ) *
      Real.sqrt (1-(x : ℝ)^2)^(k+j+2))
  simp only [NNReal.smul_def, smul_eq_mul] at hw
  rw [← hw, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [eval_dunklXuDisk_diskCoordinates β n k v.1 v.2 v.1.property,
    eval_dunklXuDisk_diskCoordinates β m j v.1 v.2 v.1.property]
  simp only [map_pow, eval_X, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, pow_add, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

/-- In the maximal inner-index step the radius power is exactly the target
outer weight, with no residual polynomial factor. -/
theorem integralInner_y_sq_dunklXuDisk_inner_add_two {β : ℝ} (hβ : -1 < β)
    (n k m : ℕ) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (X 1 ^ 2 * dunklXuDisk β n k) (dunklXuDisk β m (k + 2))) =
    Polynomial.integralInner (jacobiMeasure (β + (k + 2 : ℕ) + 1 / 2) (β + (k + 2 : ℕ) + 1 / 2)) (Polynomial.IntegrablePair.of (jacobiMeasure (β + (k + 2 : ℕ) + 1 / 2) (β + (k + 2 : ℕ) + 1 / 2)) (jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)) (jacobi (β + (k + 2 : ℕ) + 1 / 2) (β + (k + 2 : ℕ) + 1 / 2) (m - (k + 2))) (h := (hasFiniteMoments_jacobiMeasure (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]) (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])).integrable_mul _ _)) *
    Polynomial.integralInner (jacobiMeasure β β) (Polynomial.IntegrablePair.of (jacobiMeasure β β) (Polynomial.X ^ 2 * jacobi β β k) (jacobi β β (k + 2))) := by
  rw [integralInner_y_sq_dunklXuDisk_separated hβ]
  congr 1
  let a := β + ((k + 2 : ℕ) : ℝ) + 1/2
  have ha : -1 < a := by dsimp [a]; have := Nat.cast_nonneg (α := ℝ) (k+2); linarith
  rw [Polynomial.integralInner, integral_jacobiMeasure a a
    ⟨_, (hasFiniteMoments_jacobiMeasure ha ha).integrable_mul _ _⟩]
  apply integral_congr_ae
  filter_upwards [] with x
  have hs : 0 ≤ 1 - (x : ℝ)^2 := by nlinarith [x.property.1, x.property.2]
  rw [show a = (β + 1/2) + (k+2 : ℕ) by dsimp [a]; ring,
    jacobiWeight_add_nat,
    show k + (k + 2) + 2 = 2 * (k + 2) by omega, pow_mul, Real.sq_sqrt hs]
  ring

/-- The inner maximal-degree pairing is strictly positive. -/
theorem integralInner_X_sq_jacobi_add_two_pos {β : ℝ} (hβ : -1 < β) (k : ℕ) :
    0 < Polynomial.integralInner (jacobiMeasure β β) (Polynomial.IntegrablePair.of (jacobiMeasure β β) (Polynomial.X ^ 2 * jacobi β β k) (jacobi β β (k + 2))) := by
  have h := (isOrthogonal_jacobiSequence hβ hβ).integralInner_pos_of_degree_eq
    (hasFiniteMoments_jacobiMeasure hβ hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ)
    (p := Polynomial.X ^ 2 * jacobi β β k) (n := k + 2)
  apply h
  · rw [degree_mul, degree_pow, degree_X,
      degree_jacobi_of_neg_one_lt hβ hβ]
    push_cast
    ring
  · rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_X, one_pow, one_mul]
    rw [leadingCoeff, show (jacobi β β k).natDegree = k from (jacobiSequence hβ hβ).natDegree_eq k]
    exact coeff_jacobi_self_pos hβ hβ k
  · change 0 < (jacobi β β (k + 2)).leadingCoeff
    rw [leadingCoeff, show (jacobi β β (k + 2)).natDegree = k + 2 from
      (jacobiSequence hβ hβ).natDegree_eq (k + 2)]
    exact coeff_jacobi_self_pos hβ hβ (k + 2)

end MvPolynomial
