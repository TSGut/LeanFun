/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.StandardMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalPositive
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalShift
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.Moments
import Mathlib.Topology.Algebra.Polynomial

/-! # Product-coordinate measure for Proriol polynomials
Mixed-family pairings separate under the Duffy map (x,z) -> (x,xz).
This auxiliary measure retains the Jacobi masses. Its constant factor relative to
DLMF 18.37.8 is tracked separately from the polynomial normalization.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- The Proriol pairing separates into inner Jacobi and radial pairings. -/
theorem integralInner_proriol_mixed_parameters (α β γ : ℝ) {α' β' γ' : ℝ}
    (hα : -1 < α') (hβ : -1 < β') (hγ : -1 < γ') (n k m j : ℕ) :
    integralInner (proriolProductMeasure α' β' γ') (IntegrablePair.of (proriolProductMeasure α' β' γ') (proriol α β γ n k) (proriol α' β' γ' m j)) =
      (∫ x, (shiftedJacobi α (β + γ + 2 * k + 1) (n-k)).eval x *
        (shiftedJacobi α' (β' + γ' + 2 * j + 1) (m-j)).eval x * x ^ (k+j)
        ∂unitJacobiMeasure α' (β'+γ'+1)) *
      Polynomial.integralInner (unitJacobiMeasure β' γ') (Polynomial.IntegrablePair.of (unitJacobiMeasure β' γ') (shiftedJacobi β γ k) (shiftedJacobi β' γ' j)) := by
  let := isFiniteMeasure_unitJacobiMeasure hα (show -1 < β'+γ'+1 by linarith)
  let := isFiniteMeasure_unitJacobiMeasure hβ hγ
  have hi := (koornwinderMeasure_integral_univ (fun x => x) continuous_id
    (unitJacobiMeasure α' (β'+γ'+1)) (unitJacobiMeasure β' γ')
    ⟨fun v ↦ eval v (proriol α β γ n k * proriol α' β' γ' m j), by
      simpa only [proriolProductMeasure, map_one, mul_one] using
        (hasFiniteMoments_proriolProductMeasure hα hβ hγ).integrable_mul (proriol α β γ n k * proriol α' β' γ' m j) 1⟩).2
  simp only [map_mul] at hi
  simp only [integralInner, proriolProductMeasure]
  rw [hi,
    Polynomial.integralInner,
    ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [eval_proriol_scaled, eval_proriol_scaled, pow_add]
  ring

/-- The raw same-index connection pairing has positive sign for every admissible parameter pair. -/
theorem integralInner_proriol_diag_pos {α β γ α' β' γ' : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ)
    (hα' : -1 < α') (hβ' : -1 < β') (hγ' : -1 < γ') (n k : ℕ) :
    0 < integralInner (proriolMeasure α' β' γ') (IntegrablePair.of (proriolMeasure α' β' γ') (proriol α β γ n k) (proriol α' β' γ' n k)) := by
  rw [integralInner, integral_proriolMeasure _ _ _ ⟨_, (hasFiniteMoments_proriolProductMeasure hα' hβ' hγ').integrable_mul _ _⟩]
  apply mul_pos (by positivity)
  change 0 < integralInner (proriolProductMeasure α' β' γ') (IntegrablePair.of (proriolProductMeasure α' β' γ') _ _)
  rw [integralInner_proriol_mixed_parameters α β γ hα' hβ' hγ']
  apply mul_pos _ (integralInner_shiftedJacobi_diag_pos hβ hγ hβ' hγ' k)
  rw [show k+k=2*k by omega]
  simp_rw [mul_comm (_ * _) (_ ^ _)]
  rw [(integral_pow_unitJacobiMeasure_integrable α' (β'+γ'+1) (2*k) ⟨_, (hasFiniteMoments_unitJacobiMeasure hα' (by have := Nat.cast_nonneg (α := ℝ) (2*k); linarith)).integrable_mul _ _⟩ (by dsimp only; fun_prop)).2]
  have he : β'+γ'+1+(↑(2*k) : ℝ) = β'+γ'+2*k+1 := by push_cast; ring
  simp only
  rw [he]
  apply mul_pos (by positivity)
  exact integralInner_shiftedJacobi_diag_pos hα
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) hα'
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) (n-k)

end MvPolynomial
