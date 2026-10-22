/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.EvenQuadraticElimination

/-! # Arbitrary nonzero quadratic vertical coefficients
Scaling restores the coefficient of y² after the sign argument was normalized
to one. It may have either sign. Reference: finite matrix path expansion.
-/

public section
open Matrix Filter
open scoped Topology
namespace MvPolynomial

/-- Normalize the y² coefficient by factoring it out of every multiplication entry. -/
theorem dunklXuQuadraticMatrix_scale {β : ℝ} (hβ : -1 < β) (u v : ℝ) (hv : v ≠ 0)
    (i j : Σ n : ℕ, Fin (n + 1)) :
    dunklXuQuadraticMatrix hβ u v i j = v * dunklXuQuadraticMatrix hβ (u / v) 1 i j := by
  have he : (C v * X 1 ^ 2 - C u * (1 - X 0 ^ 2) : MvPolynomial (Fin 2) ℝ) =
      v • (C 1 * X 1 ^ 2 - C (u / v) * (1 - X 0 ^ 2)) := by
    conv_rhs =>
      rw [smul_eq_C_mul, map_one, one_mul, mul_sub,
        ← mul_assoc (C v) (C (u / v)), ← map_mul]
    rw [show v * (u / v) = u by field_simp]
  unfold dunklXuQuadraticMatrix
  simp only [he, smul_mul_assoc]
  rw [integralInner_smul_left (h := (hasFiniteMoments_dunklXuDiskMeasure hβ).integrable_mul _ _)]

/-- The first possible power sandwich scales by the coefficient once per edge. -/
theorem dunklXuInteriorFunctional_pow_scale {β : ℝ} (hβ : -1 < β)
    (u v : ℝ) (hv : v ≠ 0) (r q : ℕ) :
    dunklXuInteriorFunctional hβ u v r (dunklXuInteriorMatrix hβ u v r ^ q) =
      v ^ (q + 2) * dunklXuInteriorFunctional hβ (u / v) 1 r
        (dunklXuInteriorMatrix hβ (u / v) 1 r ^ q) := by
  have hK : dunklXuInteriorMatrix hβ u v r = v • dunklXuInteriorMatrix hβ (u / v) 1 r := by
    ext i j
    exact dunklXuQuadraticMatrix_scale hβ u v hv _ _
  have hF (i : DunklXuEvenInterior r) : dunklXuInteriorLeft hβ u v r i =
      v * dunklXuInteriorLeft hβ (u / v) 1 r i := dunklXuQuadraticMatrix_scale hβ u v hv _ _
  have hG (i : DunklXuEvenInterior r) : dunklXuInteriorRight hβ u v r i =
      v * dunklXuInteriorRight hβ (u / v) 1 r i := dunklXuQuadraticMatrix_scale hβ u v hv _ _
  rw [hK, smul_pow]
  change (∑ i, ∑ j, dunklXuInteriorLeft hβ u v r i *
    (v ^ q * (dunklXuInteriorMatrix hβ (u / v) 1 r ^ q) i j) * dunklXuInteriorRight hβ u v r j) = _
  simp_rw [hF, hG]
  change _ = v ^ (q + 2) * (∑ i, ∑ j, dunklXuInteriorLeft hβ (u / v) 1 r i *
    (dunklXuInteriorMatrix hβ (u / v) 1 r ^ q) i j * dunklXuInteriorRight hβ (u / v) 1 r j)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- Every nonzero y² coefficient gives a surviving first path coefficient,
regardless of its sign or of the x-only quadratic coefficient. -/
theorem dunklXuInterior_first_coefficient_ne_zero_of_vertical_ne_zero {β : ℝ}
    (hβ : -1 < β) (u v : ℝ) (hv : v ≠ 0) (r : ℕ) (hr : 2 ≤ r) :
    dunklXuInteriorFunctional hβ u v r (dunklXuInteriorMatrix hβ u v r ^ (r - 2)) ≠ 0 := by
  rw [dunklXuInteriorFunctional_pow_scale hβ u v hv]
  exact mul_ne_zero (pow_ne_zero _ hv) (dunklXuInterior_first_coefficient_ne_zero hβ (u / v) r hr)

/-- The finite inverse sandwich remains nonzero locally for any nonzero
vertical coefficient; no continuity of a Cholesky factor is assumed. -/
theorem eventually_dunklXuInterior_inverse_ne_zero_of_vertical_ne_zero {β : ℝ}
    (hβ : -1 < β) (u v : ℝ) (hv : v ≠ 0) (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      dunklXuInteriorFunctional hβ u v r ((1 + t • dunklXuInteriorMatrix hβ u v r)⁻¹) ≠ 0 := by
  apply eventually_apply_inv_one_add_smul_ne_zero _ _ (r - 2)
  · intro q hq
    exact dunklXuInterior_sandwich_eq_zero hβ u v r q (by omega)
  · exact dunklXuInterior_first_coefficient_ne_zero_of_vertical_ne_zero hβ u v hv r hr

end MvPolynomial
