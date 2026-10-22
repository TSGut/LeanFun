/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Proriol.Basic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalShift
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Moments
import Mathlib.Topology.Algebra.Polynomial

/-! # Product-coordinate measure for Proriol polynomials
The Duffy map (x,z) -> (x,xz) sends two affine Jacobi measures to the triangle.
This auxiliary measure retains the Jacobi masses. Its constant factor relative to
DLMF 18.37.8 is tracked separately from the polynomial normalization.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- The product-coordinate Proriol measure, before removing the affine mass factor. -/
noncomputable def proriolProductMeasure (α β γ : ℝ) : Measure (Fin 2 → ℝ) :=
  koornwinderMeasure (fun x : (Set.univ : Set ℝ) ↦ (x : ℝ))
    (Measure.comap Subtype.val (unitJacobiMeasure α (β + γ + 1)))
    (unitJacobiMeasure β γ) (input := by
      let : SFinite (unitJacobiMeasure β γ) := by
        let : SFinite (jacobiMeasure β γ) :=
          sFinite_openIntervalWeightMeasure (-1) 1 (jacobiWeight β γ)
        unfold unitJacobiMeasure
        infer_instance
      exact KoornwinderMeasureInput.ofContinuous _ _ continuous_subtype_val)

/-- Polynomial moments are finite throughout the Jacobi parameter range. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_proriolProductMeasure {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) :
    HasFiniteMoments (proriolProductMeasure α β γ) := by
  exact hasFiniteMoments_koornwinderMeasure
    (by simpa only [map_comap_subtype_coe MeasurableSet.univ, Measure.restrict_univ] using
      (hasFiniteMoments_unitJacobiMeasure hα (show -1 < β+γ+1 by linarith)))
    (hasFiniteMoments_unitJacobiMeasure hβ hγ) continuous_subtype_val
    (Polynomial.X ^ 2) (by filter_upwards [] with x; simp)

/-- The Proriol pairing separates into inner Jacobi and radial pairings. -/
theorem integralInner_proriol_separated {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n k m j : ℕ) :
    integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) (proriol α β γ n k) (proriol α β γ m j)) =
      (∫ x, (shiftedJacobi α (β + γ + 2 * k + 1) (n-k)).eval x *
        (shiftedJacobi α (β + γ + 2 * j + 1) (m-j)).eval x * x ^ (k+j)
        ∂unitJacobiMeasure α (β+γ+1)) *
      Polynomial.integralInner (jacobiMeasure β γ) (Polynomial.IntegrablePair.of (jacobiMeasure β γ) (jacobi β γ k) (jacobi β γ j)) := by
  let := isFiniteMeasure_unitJacobiMeasure hα (show -1 < β+γ+1 by linarith)
  let := isFiniteMeasure_unitJacobiMeasure hβ hγ
  have hi := (koornwinderMeasure_integral_univ (fun x => x) continuous_id
    (unitJacobiMeasure α (β+γ+1)) (unitJacobiMeasure β γ)
    ⟨fun v ↦ eval v (proriol α β γ n k * proriol α β γ m j), by
      simpa only [proriolProductMeasure, map_one, mul_one] using
        (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul (proriol α β γ n k * proriol α β γ m j) 1⟩).2
  simp only [map_mul] at hi
  simp only [integralInner, proriolProductMeasure]
  rw [hi,
    ← integralInner_shiftedJacobi β γ k j
      (hi := (hasFiniteMoments_jacobiMeasure hβ hγ).integrable_mul _ _), Polynomial.integralInner,
    ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [eval_proriol_scaled, eval_proriol_scaled, pow_add]
  ring

/-- Equal inner degrees shift the outer Jacobi parameter by twice that degree. -/
theorem integralInner_proriol_same_inner {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n m k : ℕ) :
    integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) (proriol α β γ n k) (proriol α β γ m k)) =
      ((2 : ℝ) ^ (2*k))⁻¹ *
        Polynomial.integralInner (jacobiMeasure α (β+γ+2*k+1)) (Polynomial.IntegrablePair.of (jacobiMeasure α (β+γ+2*k+1)) (jacobi α (β+γ+2*k+1) (n-k)) (jacobi α (β+γ+2*k+1) (m-k)) (h := (hasFiniteMoments_jacobiMeasure hα (by have := Nat.cast_nonneg (α := ℝ) k; linarith)).integrable_mul _ _)) *
        Polynomial.integralInner (jacobiMeasure β γ) (Polynomial.IntegrablePair.of (jacobiMeasure β γ) (jacobi β γ k) (jacobi β γ k)) := by
  rw [integralInner_proriol_separated hα hβ hγ]
  congr 1
  have he : β + γ + 1 + (↑(2*k) : ℝ) = β + γ + 2*k + 1 := by push_cast; ring
  rw [show k+k=2*k by omega]
  simp_rw [mul_comm (_ * _) (_ ^ _)]
  rw [(integral_pow_unitJacobiMeasure_integrable α (β+γ+1) (2*k) ⟨_, (hasFiniteMoments_unitJacobiMeasure hα (by have := Nat.cast_nonneg (α := ℝ) (2*k); linarith)).integrable_mul _ _⟩ (by dsimp only; fun_prop)).2]
  simp only
  rw [he]
  congr 1
  exact integralInner_shiftedJacobi _ _ _ _
    (hi := (hasFiniteMoments_jacobiMeasure hα (by have := Nat.cast_nonneg (α := ℝ) k; linarith)).integrable_mul _ _)

end MvPolynomial
