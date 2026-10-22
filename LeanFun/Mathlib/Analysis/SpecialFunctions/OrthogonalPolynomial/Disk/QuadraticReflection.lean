/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Reflection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.QuadraticPadding
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.GramFactor
public import LeanFun.Mathlib.LinearAlgebra.Matrix.GramFactorSectors
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.MeasureModification

/-! # Canonical quadratic Gram factors preserve Cartesian parity
The modification is the existing coordinateQuadratic. Both reflection zeros
pass to the canonical positive triangular factor, in the complete ordered basis.
Reference: Cholesky elimination and Cartesian orthogonal polynomial symmetry.
-/

public section
open MeasureTheory Set Polynomial Module Matrix
namespace MvPolynomial.CartesianDiskSystem
variable {μ ν : Measure ℝ} (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)

/-- Distinct Cartesian parity labels have zero quadratic-modified Gram entries. -/
theorem integralInner_coordinateQuadratic_eq_zero_of_parity [SFinite ν]
    [μ.IsNegInvariant] [ν.IsNegInvariant] (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hμ : Polynomial.HasFiniteMoments μ) (hpos : Polynomial.HasPositiveDefiniteIntegral μ)
    (A B C : ℝ) (n k m j : ℕ)
    (hne : ((n - k) % 2, k % 2) ≠ ((m - j) % 2, j % 2)) :
    integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (coordinateQuadratic A B C * S.polynomial n k) (S.polynomial m j)) = 0 := by
  by_cases hinner : k % 2 = j % 2
  · apply S.integralInner_mul_polynomial_eq_zero_of_outer_parity hx hμ hpos
      (coordinateQuadratic A B C) (fun x z ↦ by simp [coordinateQuadratic, diskCoordinates, mul_pow])
    exact fun houter ↦ hne (Prod.ext houter hinner)
  · exact S.integralInner_mul_polynomial_eq_zero_of_inner_parity hx
      (coordinateQuadratic A B C) (fun x z ↦ by simp [coordinateQuadratic, diskCoordinates, mul_pow])
      n k m j hinner

/-- The canonical full quadratic-modified Gram factor inherits the parity zeros.
The indexing and ordering are those of the supplied polynomial basis. -/
theorem integralGramFactor_coordinateQuadratic_eq_zero_of_parity
    [SFinite ν] [μ.IsNegInvariant] [ν.IsNegInvariant]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hμ : Polynomial.HasFiniteMoments μ) (hpos : Polynomial.HasPositiveDefiniteIntegral μ)
    (A B C : ℝ)
    (hu : ∀ᵐ x ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν), 0 ≤ eval x (coordinateQuadratic A B C))
    (hM : MvPolynomial.HasFiniteMoments (MvPolynomial.polynomialDensityMeasure ((coordinateQuadratic A B C)) (((cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν))).comap Subtype.val)))
    (hP : MvPolynomial.HasPositiveDefiniteIntegral (MvPolynomial.polynomialDensityMeasure ((coordinateQuadratic A B C)) (((cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν))).comap Subtype.val)))
    {N : ℕ} {V : Submodule ℝ (MvPolynomial (Fin 2) ℝ)} (b : Basis (Fin N) ℝ V)
    (n k : Fin N → ℕ) (hb : ∀ i, (b i : MvPolynomial (Fin 2) ℝ) = S.polynomial (n i) (k i))
    (i j : Fin N) (hne : ((n i - k i) % 2, k i % 2) ≠ ((n j - k j) % 2, k j % 2)) :
    integralGramFactor _ hM hP b i j = 0 := by
  obtain ⟨hR, hd, hG⟩ := integralGramFactor_spec _ hM hP b
  apply hR.apply_eq_zero_of_gram_sectors (fun i ↦ (hd i).ne')
    (fun i ↦ ((n i - k i) % 2, k i % 2)) _ i j hne
  intro a c hac
  rw [← hG]
  change integralInner _ (IntegrablePair.of _ (b a : MvPolynomial (Fin 2) ℝ) (b c : MvPolynomial (Fin 2) ℝ) (h := hM.integrable_mul _ _)) = 0
  simp only [hb]
  rw [MvPolynomial.integralInner_withDensity_polynomial _ _ _ hu
    (hpq := (S.hasFiniteMoments hx).integrable_mul _ _)]
  exact S.integralInner_coordinateQuadratic_eq_zero_of_parity hx hμ hpos A B C _ _ _ _ hac

end MvPolynomial.CartesianDiskSystem
