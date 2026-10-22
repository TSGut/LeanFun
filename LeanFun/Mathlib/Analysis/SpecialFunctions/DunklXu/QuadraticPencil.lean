/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticMatrix
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.CartesianSystem
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.DeformationSystem
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.QuadraticPadding

/-! # The deformed-measure Gram matrix is the concrete quadratic pencil
The canonical Cartesian even-even polynomials identify the abstract deformation
formula with the normalized Dunkl--Xu matrix used in the noncancellation proof.
Reference: Cartesian measure transport and finite Gram factorizations.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- An affine quadratic density gives the expected identity-plus-perturbation Gram entries. -/
theorem integral_affine_quadratic_normalizedDunklXuBasis {β : ℝ} (hβ : -1 < β)
    (d u v t : ℝ) (i j : Σ n : ℕ, Fin (n + 1)) :
    (∫ x, (d + t * (v * (x 1) ^ 2 - u * (1 - (x 0) ^ 2))) *
      (eval x (normalizedDunklXuBasis hβ i) * eval x (normalizedDunklXuBasis hβ j))
      ∂dunklXuDiskMeasure β) =
      d * (if i = j then 1 else 0) + t * dunklXuQuadraticMatrix hβ u v i j := by
  have he : (∫ x, (d + t * (v * (x 1) ^ 2 - u * (1 - (x 0) ^ 2))) *
      (eval x (normalizedDunklXuBasis hβ i) * eval x (normalizedDunklXuBasis hβ j))
      ∂dunklXuDiskMeasure β) =
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) ((d • normalizedDunklXuBasis hβ i) +
        t • ((C v * X 1 ^ 2 - C u * (1 - X 0 ^ 2)) * normalizedDunklXuBasis hβ i)) (normalizedDunklXuBasis hβ j)) := by
    unfold integralInner
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [map_add, map_mul, map_sub, map_pow, map_one, eval_C, eval_X, smul_eq_C_mul]
    ring
  rw [he, integralInner_add_left (hasFiniteMoments_dunklXuDiskMeasure hβ),
    integralInner_smul_left (h := (hasFiniteMoments_dunklXuDiskMeasure hβ).integrable_mul _ _), integralInner_smul_left (h := (hasFiniteMoments_dunklXuDiskMeasure hβ).integrable_mul _ _), integralInner_normalizedDunklXuBasis]
  rfl

/-- Actual deformed Cartesian quadratic Gram entries equal the concrete
normalized disk affine pencil, throughout the admissible deformation range. -/
theorem integral_quadratic_deformed_eq_dunklXu_pencil {β : ℝ} (hβ : -1 < β)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδpos : Polynomial.HasPositiveDefiniteIntegral
      (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val)))
    (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β))
    (a b c d : ℕ) (A B C : ℝ) :
    (∫ x, (A + B * (x 0) ^ 2 + C * (x 1) ^ 2) *
      (eval x (T.polynomial (2 * a + 2 * b) (2 * b)) *
        eval x (T.polynomial (2 * c + 2 * d) (2 * d)))
      ∂cartesianDiskMeasure
        (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (ProductMeasureInput.ofSFinite (hν := by infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β))) =
      (A + B) * (if (a, b) = (c, d) then 1 else 0) +
        δ * dunklXuQuadraticMatrix hβ B C
          ⟨2 * a + 2 * b, ⟨2 * b, by omega⟩⟩ ⟨2 * c + 2 * d, ⟨2 * d, by omega⟩⟩ := by
  have hβ' : -1 < β + 1 / 2 := by linarith
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isFiniteMeasure_jacobiMeasure hβ' hβ'
  let := isNegInvariant_jacobiMeasure (β + 1 / 2)
  let S := dunklXuCartesianSystem hβ
  rw [S.integral_quadratic_polynomial_diskDeformation
    (ae_mem_Icc_jacobiMeasure _ _) (ae_mem_Icc_jacobiMeasure _ _)
    (hasFiniteMoments_jacobiMeasure hβ' hβ') (hasPositiveDefiniteIntegral_jacobiMeasure hβ' hβ')
    (hasFiniteMoments_jacobiMeasure hβ hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ)
    hδ hδ1 hδpos T a b c d A B C]
  rw [← normalizedDunklXuBasis_eq_cartesian hβ S ⟨2 * a + 2 * b, ⟨2 * b, by omega⟩⟩,
    ← normalizedDunklXuBasis_eq_cartesian hβ S ⟨2 * c + 2 * d, ⟨2 * d, by omega⟩⟩]
  change (∫ x, _ ∂dunklXuDiskMeasure β) = _
  rw [integral_affine_quadratic_normalizedDunklXuBasis]
  congr 2
  congr 1
  apply propext
  constructor
  · intro h
    have hn := congrArg Sigma.fst h
    have hk := congrArg (fun i : Σ n : ℕ, Fin (n + 1) ↦ (i.2 : ℕ)) h
    exact Prod.ext (by dsimp at hn hk; omega) (by dsimp at hk; omega)
  · intro h
    cases h
    rfl

end MvPolynomial
