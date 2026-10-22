/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.WeightedPreconditioner
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.FirstOrderRepresentation
/-! # Reconstruction after weighted ultraspherical preconditioning
Reference: Olver--Townsend (2013), Section 4.1. Right preconditioning gains
one degree weight, and the represented Chebyshev series converges uniformly.
-/
@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open ContinuousLinearMap Filter
open scoped Topology

/-- Degree-weight multiplier associated with reciprocal-degree preconditioning. -/
def degreeGainDiagonal (n : ℕ) : ℂ := ((n : ℂ) + 1) * firstOrderDiagonal n

/-- The gain in degree weight is bounded by two. -/
theorem norm_degreeGainDiagonal_le (n : ℕ) : ‖degreeGainDiagonal n‖ ≤ 2 := by
  cases n with
  | zero => norm_num [degreeGainDiagonal]
  | succ n =>
    have he : degreeGainDiagonal (n + 1) =
        (((n : ℝ) + 2) / ((n : ℝ) + 1) : ℝ) := by
      simp only [degreeGainDiagonal, firstOrderDiagonal_succ]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by positivity)).2
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Right preconditioning gains one degree weight. -/
def weightedUltrasphericalReconstruction (s k : ℕ) :
    lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 (s + 1) :=
  (ultrasphericalDerivativeScale k)⁻¹ •
    (lp.degreeWeightedL2Isometry (s + 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((lp.coefficientDiagonal degreeGainDiagonal (by norm_num) norm_degreeGainDiagonal_le).comp
        (lp.degreeWeightedL2Isometry s).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Coordinate formula for the map gaining one degree weight. -/
theorem weightedUltrasphericalReconstruction_apply (s k : ℕ) (x : lp.DegreeWeightedL2 s) (n : ℕ) :
    (weightedUltrasphericalReconstruction s k x).1 n =
      (ultrasphericalDerivativeScale k)⁻¹ * firstOrderDiagonal n * x.1 n := by
  change (ultrasphericalDerivativeScale k)⁻¹ *
    (degreeGainDiagonal n * (((n : ℂ) + 1)^s * x.1 n) / ((n : ℂ) + 1)^(s + 1)) = _
  simp only [degreeGainDiagonal, pow_succ]
  field_simp


/-- The gained-weight reconstruction has the original right-preconditioned coefficients. -/
theorem weightedUltrasphericalReconstruction_eq (s k : ℕ) (x : lp.DegreeWeightedL2 s) (n : ℕ) :
    (weightedUltrasphericalReconstruction s k x).1 n =
      (weightedUltrasphericalPreconditioner s k x).1 n := by
  rw [weightedUltrasphericalReconstruction_apply]
  change _ = (ultrasphericalDerivativeScale k)⁻¹ * (weightedFirstOrderPreconditioner s x).1 n
  rw [weightedFirstOrderPreconditioner_apply]
  ring

/-- The classical Chebyshev series represented by right-preconditioned coefficients. -/
def weightedUltrasphericalFunction (s k : ℕ) (x : lp.DegreeWeightedL2 s)
    (t : Set.Icc (-1 : ℝ) 1) : ℂ :=
  complexChebyshevSeries
    (firstOrderPreconditioner ((ultrasphericalDerivativeScale k)⁻¹ • lp.degreeWeightedInclusion s x))
    (.ofFirstOrder ((ultrasphericalDerivativeScale k)⁻¹ • lp.degreeWeightedInclusion s x) t)

/-- The reconstructed function is the sum of the right-preconditioned Chebyshev series. -/
theorem hasSum_weightedUltrasphericalFunction (s k : ℕ) (x : lp.DegreeWeightedL2 s)
    (t : Set.Icc (-1 : ℝ) 1) :
    HasSum (fun n ↦ (weightedUltrasphericalPreconditioner s k x).1 n *
      (T ℂ n).eval (t.val : ℂ)) (weightedUltrasphericalFunction s k x t) := by
  let y := (ultrasphericalDerivativeScale k)⁻¹ • lp.degreeWeightedInclusion s x
  have hs := summable_chebyshevSeries_of_absolute
    (summable_norm_firstOrderPreconditioner y).1 t
  have he (n : ℕ) : firstOrderPreconditioner y n =
      (weightedUltrasphericalPreconditioner s k x).1 n := by
    rw [firstOrderPreconditioner_apply]
    change firstOrderDiagonal n * ((ultrasphericalDerivativeScale k)⁻¹ *
      lp.degreeWeightedInclusion s x n) =
      (ultrasphericalDerivativeScale k)⁻¹ * (weightedFirstOrderPreconditioner s x).1 n
    rw [lp.degreeWeightedInclusion_apply, weightedFirstOrderPreconditioner_apply]
    ring
  change HasSum _ (complexChebyshevSeries (firstOrderPreconditioner y) (.ofFirstOrder y t))
  rw [complexChebyshevSeries_eq_tsum (.ofFirstOrder y t) hs]
  simpa only [he, ComplexChebyshevSeriesPoint.ofFirstOrder_val] using hs.hasSum

/-- Weighted coefficient convergence gives uniform convergence of reconstructed functions. -/
theorem tendstoUniformly_weightedUltrasphericalFunction (s k : ℕ)
    {ι : Type*} {l : Filter ι} {v : ι → lp.DegreeWeightedL2 s}
    {x : lp.DegreeWeightedL2 s} (hv : Tendsto v l (𝓝 x)) :
    TendstoUniformly (fun n ↦ weightedUltrasphericalFunction s k (v n))
      (weightedUltrasphericalFunction s k x) l := by
  apply tendstoUniformlyOn_firstOrder_reconstruction
  exact (((lp.degreeWeightedInclusion s).continuous.tendsto x).comp hv).const_smul _
end Polynomial.Chebyshev
