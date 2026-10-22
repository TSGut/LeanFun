/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.ClassicalMeasure
import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.DiskOuterMeasure
import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.ModificationDensity
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Disk weight raising as polynomial measure modification

Raising the disk parameter multiplies the measure by `1-x²-y²`. This links
Cartesian parameter conversion to the general polynomial Gram factorization.
Reference: Dunkl–Xu; Gutleb–Olver–Slevinsky, polynomial measure modifications.
-/

@[expose] public section
open MeasureTheory Polynomial Set
namespace MvPolynomial

/-- The polynomial vanishing on the unit circle. -/
noncomputable def diskBoundary : MvPolynomial (Fin 2) ℝ := 1 - X 0 ^ 2 - X 1 ^ 2

/-- The unit disk parameter shift is precisely a boundary-polynomial density
change, stated for every continuous test function. -/
theorem integral_dunklXuDiskMeasure_add_one {β : ℝ} (hβ : -1 < β)
    {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    ∫ v, f v ∂dunklXuDiskMeasure (β + 1) =
      ∫ v, eval v diskBoundary * f v ∂dunklXuDiskMeasure β := by
  have hα : -1 < β+1/2 := by linarith
  have hu : cartesianDiskModification 1 (1-Polynomial.X^2) 1 = diskBoundary := by
    norm_num [cartesianDiskModification, cartesianDiskPolynomial, diskBoundary,
      diskLift, Finset.sum_range_succ, Polynomial.coeff_one]
    ring
  have houter : diskOuterModification 1 1
      ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val) =
        jacobiMeasure ((β+1/2)+1) ((β+1/2)+1) := by
    exact (congrArg (fun p : ℝ[X] ↦ polynomialDensityMeasure p
      ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val))
      (mul_one ((1-Polynomial.X^2)^1))).trans (by simpa only [diskOuterMeasure, Nat.cast_one] using diskOuterMeasure_jacobi (β+1/2) 1)
  have hinner : Polynomial.polynomialDensityMeasure (1-Polynomial.X^2)
      ((jacobiMeasure β β).comap Subtype.val) = jacobiMeasure (β+1) (β+1) := by
    exact (congrArg (fun p : ℝ[X] ↦ polynomialDensityMeasure p
      ((jacobiMeasure β β).comap Subtype.val))
      (pow_one (1-Polynomial.X^2)).symm).trans (by simpa only [diskOuterMeasure, Nat.cast_one] using diskOuterMeasure_jacobi β 1)
  have hg : ∀ᵐ x ∂jacobiMeasure β β, 0 ≤ (1-Polynomial.X^2 : ℝ[X]).eval x := by
    filter_upwards [ae_mem_Icc_jacobiMeasure β β] with x hx
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith [hx.1,hx.2]
  have hdeg : (1-Polynomial.X^2 : ℝ[X]).natDegree ≤ 2*1 := by compute_degree
  have hpar : ∀ i, i%2 ≠ 0 → (1-Polynomial.X^2 : ℝ[X]).coeff i = 0 := by
    intro i hi
    have h0 : i ≠ 0 := by omega
    have h2 : i ≠ 2 := by omega
    simp [Polynomial.coeff_sub, Polynomial.coeff_one, h0, h2]
  have he := integral_cartesianDiskModification
    (hasFiniteMoments_jacobiMeasure hα hα) (hasFiniteMoments_jacobiMeasure hβ hβ)
    (ae_mem_Icc_jacobiMeasure _ _) (ae_mem_Icc_jacobiMeasure _ _)
    1 (1-Polynomial.X^2) 1 (by filter_upwards [] with x; simp) hg hdeg hpar hf
  simp only [cartesianDiskMeasure] at he
  simp only [houter, hinner, hu] at he
  simpa only [dunklXuDiskMeasure, cartesianDiskMeasure, show β+1/2+1 = β+1+1/2 by ring] using he

/-- Polynomial pairings for the raised parameter are the modified Gram pairings. -/
theorem integralInner_dunklXuDiskMeasure_add_one {β : ℝ} (hβ : -1 < β)
    (p q : MvPolynomial (Fin 2) ℝ) :
    integralInner (dunklXuDiskMeasure (β + 1)) (IntegrablePair.of (dunklXuDiskMeasure (β + 1)) p q (h := (hasFiniteMoments_dunklXuDiskMeasure (by linarith)).integrable_mul _ _)) =
      integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (diskBoundary * p) q) := by
  rw [integralInner, integral_dunklXuDiskMeasure_add_one hβ
    (show Continuous (fun v => eval v p * eval v q) from p.continuous_eval.mul q.continuous_eval)]
  simp only [integralInner, map_mul, mul_assoc]

end MvPolynomial
