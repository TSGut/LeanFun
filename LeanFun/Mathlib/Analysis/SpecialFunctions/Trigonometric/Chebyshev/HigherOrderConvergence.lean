/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.HigherOrder
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.WeightedReconstruction
/-! # Convergence of higher-order ultraspherical finite solves
Reference: Olver--Townsend (2013), Section 4.1. The infinite bordered operator
is assumed invertible. Every finite inverse is evaluated on its certified domain.
-/
@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open ContinuousLinearMap Filter
open scoped Topology

/-- The lifted finite section of a preconditioned polynomial differential system. -/
def weightedUltrasphericalFiniteSection (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (n : ℕ) : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  liftedFiniteSection (lp.degreeWeightedProjection s n) (weightedUltrasphericalRemainder s k B a₀ a)

/-- The finite solution at a certified invertible cutoff. -/
def weightedUltrasphericalFiniteSolution (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (n : Ring.InvertibleIndex (weightedUltrasphericalFiniteSection s k B a₀ a))
    (f : lp.DegreeWeightedL2 s) : lp.DegreeWeightedL2 s :=
  Ring.inverseAt (weightedUltrasphericalFiniteSection s k B a₀ a) n
    (lp.degreeWeightedProjection s n.val f)

/-- Invertible cutoffs form a nontrivial cofinal limiting domain. -/
theorem weightedUltraspherical_filter_neBot (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (hT : IsUnit (1 + weightedUltrasphericalRemainder s k B a₀ a)) :
    NeBot (Ring.invertibleIndexFilter (weightedUltrasphericalFiniteSection s k B a₀ a) atTop) :=
  lp.degreeWeighted_system_filter_neBot s _
    (isCompactOperator_weightedUltrasphericalRemainder s k B a₀ a) hT

/-- The preconditioned coefficient error is controlled by its exact weighted tail. -/
theorem eventually_weightedUltraspherical_error_le (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (hT : IsUnit (1 + weightedUltrasphericalRemainder s k B a₀ a)) :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (weightedUltrasphericalFiniteSection s k B a₀ a n),
      ∀ x : lp.DegreeWeightedL2 s,
        ‖weightedUltrasphericalFiniteSolution s k B a₀ a ⟨n, hn⟩
            ((1 + weightedUltrasphericalRemainder s k B a₀ a) x) - x‖ ≤
          (‖(↑(hT.unit⁻¹) : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s)‖ + 1) *
            ‖lp.degreeWeightedProjection s n x - x‖ :=
  lp.eventually_degreeWeighted_system_error_le s _
    (isCompactOperator_weightedUltrasphericalRemainder s k B a₀ a) hT

/-- The original coefficient error in the stronger norm is controlled by the preconditioned tail. -/
theorem eventually_weightedUltraspherical_reconstruction_error_le (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (hT : IsUnit (1 + weightedUltrasphericalRemainder s k B a₀ a)) :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (weightedUltrasphericalFiniteSection s k B a₀ a n),
      ∀ x : lp.DegreeWeightedL2 s,
        ‖weightedUltrasphericalReconstruction s k
            (weightedUltrasphericalFiniteSolution s k B a₀ a ⟨n, hn⟩
              ((1 + weightedUltrasphericalRemainder s k B a₀ a) x)) -
            weightedUltrasphericalReconstruction s k x‖ ≤
          (‖weightedUltrasphericalReconstruction s k‖ *
            (‖(↑(hT.unit⁻¹) : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s)‖ + 1)) *
            ‖lp.degreeWeightedProjection s n x - x‖ := by
  filter_upwards [eventually_weightedUltraspherical_error_le s k B a₀ a hT] with n hn
  obtain ⟨hn, herr⟩ := hn
  refine ⟨hn, fun x ↦ ?_⟩
  rw [← map_sub]
  exact ((weightedUltrasphericalReconstruction s k).le_opNorm _).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (herr x) (norm_nonneg (weightedUltrasphericalReconstruction s k)))

/-- The original solution coefficients converge with one additional degree weight. -/
theorem tendsto_weightedUltraspherical_reconstruction (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (hT : IsUnit (1 + weightedUltrasphericalRemainder s k B a₀ a)) (x : lp.DegreeWeightedL2 s) :
    Tendsto (fun n ↦ weightedUltrasphericalReconstruction s k
      (weightedUltrasphericalFiniteSolution s k B a₀ a n
        ((1 + weightedUltrasphericalRemainder s k B a₀ a) x)))
      (Ring.invertibleIndexFilter (weightedUltrasphericalFiniteSection s k B a₀ a) atTop)
      (𝓝 (weightedUltrasphericalReconstruction s k x)) :=
  ((weightedUltrasphericalReconstruction s k).continuous.tendsto x).comp
    (tendsto_weightedUltraspherical_system_solution s k B a₀ a hT x)

/-- The represented finite solutions converge uniformly on the closed interval. -/
theorem tendstoUniformly_weightedUltraspherical_solution (s k : ℕ)
    (B : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s) (a₀ : ℝ[X]) (a : Fin k → ℝ[X])
    (hT : IsUnit (1 + weightedUltrasphericalRemainder s k B a₀ a)) (x : lp.DegreeWeightedL2 s) :
    TendstoUniformly (fun n ↦ weightedUltrasphericalFunction s k
      (weightedUltrasphericalFiniteSolution s k B a₀ a n
        ((1 + weightedUltrasphericalRemainder s k B a₀ a) x)))
      (weightedUltrasphericalFunction s k x)
      (Ring.invertibleIndexFilter (weightedUltrasphericalFiniteSection s k B a₀ a) atTop) :=
  tendstoUniformly_weightedUltrasphericalFunction s k
    (tendsto_weightedUltraspherical_system_solution s k B a₀ a hT x)
end Polynomial.Chebyshev
