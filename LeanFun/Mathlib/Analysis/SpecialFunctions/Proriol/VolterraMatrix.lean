/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraL2
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalCoordinates
public import LeanFun.Mathlib.Analysis.InnerProductSpace.FiniteMatrix
public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraApproximateSolve

/-! # Normalized finite matrices from Proriol Volterra assembly

Each column converts a normalized shifted Legendre polynomial to the finite
shifted-Jacobi (1,0) coordinates, applies D M_K E, restores reflection and the
endpoint factor, and takes normalized physical coefficients. These matrices
are exactly the bounded L² operator sections used in the convergence theorem.
Reference: Gutleb–Olver, arXiv:1906.03907, §3.1–3.2.
-/

@[expose] public noncomputable section
open Polynomial Real Set Filter
open scoped Topology Matrix InnerProductSpace
namespace MvPolynomial

/-- Finite shifted-Jacobi (1,0) coordinates of a normalized shifted Legendre input. -/
def volterraNormalizedInput (j : ℕ) : ℕ →₀ ℝ :=
  (shiftedJacobiBasis (by norm_num : (-1 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 0)).repr
    (normalizedShiftedJacobi (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) j)

/-- The normalized Galerkin matrix computed by finite polynomial Proriol assembly. -/
def volterraProriolMatrix (K : MvPolynomial (Fin 2) ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ Polynomial.integralInner (unitJacobiMeasure 0 0) (Polynomial.IntegrablePair.of (unitJacobiMeasure 0 0) (normalizedShiftedJacobi (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) i) (volterraProriolOutput K (volterraNormalizedInput j)) (h := (Polynomial.hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _))

/-- Exact equality of assembled entries and the bounded normalized coefficient matrix. -/
theorem volterraProriolMatrix_eq (K : MvPolynomial (Fin 2) ℝ) (N : ℕ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |eval z K| ≤ M) :
    volterraProriolMatrix K N = lp.initialL2Matrix
      (volterraL2CoefficientOperator K.continuous_eval.continuousOn hM hb) N := by
  funext i j
  change Polynomial.integralInner _ (Polynomial.IntegrablePair.of _ _ _ (h := (Polynomial.hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num)).integrable_mul _ _)) =
    (hilbertBasisShiftedJacobi (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (-1 : ℝ) < 0)).coefficientOperator _ _ _
  rw [HilbertBasis.coefficientOperator_single,
    ← polynomialToL2_normalizedShiftedJacobi, ← polynomialToL2_normalizedShiftedJacobi]
  have he := volterraL2Operator_proriol K (volterraNormalizedInput j) hM hb
  simp only [volterraNormalizedInput, linearCombination_shiftedJacobi_repr] at he
  rw [he, Polynomial.inner_polynomialToL2]
  rfl

/-- Matrix multiplication by the assembled matrix is precisely the physical coefficient action. -/
theorem volterraProriolMatrix_mulVec (K : MvPolynomial (Fin 2) ℝ) {N : ℕ}
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |eval z K| ≤ M)
    (v : Fin N → ℝ) (i : Fin N) :
    (volterraProriolMatrix K N *ᵥ v) i =
      volterraL2CoefficientOperator K.continuous_eval.continuousOn hM hb (lp.initialL2Vector v) i := by
  rw [volterraProriolMatrix_eq K N hM hb]
  exact lp.initialL2Matrix_mulVec _ v i

/-- The assembled second-kind matrix solves exactly the normalized projected equation. -/
theorem volterraProriolMatrix_equation_iff (K : MvPolynomial (Fin 2) ℝ) {N : ℕ}
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |eval z K| ≤ M)
    (v : Fin N → ℝ) (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    (1 - volterraProriolMatrix K N) *ᵥ v = (fun i : Fin N ↦ f i) ↔
      lp.initialL2Projection N (lp.initialL2Vector v -
        volterraL2CoefficientOperator K.continuous_eval.continuousOn hM hb (lp.initialL2Vector v)) =
          lp.initialL2Projection N f := by
  rw [volterraProriolMatrix_eq K N hM hb]
  exact lp.initialL2Matrix_equation_iff _ v f

/-- All sufficiently large assembled polynomial-kernel matrices have unique solutions. -/
theorem eventually_existsUnique_volterraProriolMatrix_solution (K : MvPolynomial (Fin 2) ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |eval z K| ≤ M) :
    ∀ᶠ N in atTop, ∀ f : lp (fun _ : ℕ ↦ ℝ) 2,
      ∃! v : Fin N → ℝ, (1 - volterraProriolMatrix K N) *ᵥ v = (fun i : Fin N ↦ f i) := by
  filter_upwards [eventually_existsUnique_volterra_projected_solution
    K.continuous_eval.continuousOn hM hb] with N hN f
  rw [volterraProriolMatrix_eq K N hM hb]
  exact lp.existsUnique_initialL2Matrix_solution _ N f (hN f)

end MvPolynomial
