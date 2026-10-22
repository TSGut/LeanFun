/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.System
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Recurrence

import Mathlib.Topology.Algebra.Polynomial

/-!
# Coordinate multiplication pairings

Separation exposes inner-index sparsity independently of total-degree bounds.
Reference: Dunkl–Xu, §2.6.1 and multivariate three-term recurrences.
-/

@[expose] public section
open MeasureTheory Polynomial
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} (S : KoornwinderSystem a ρ μ ν)

/-- Coordinate multiplication coefficients against the orthonormal family. -/
noncomputable def multiplicationEntry (coord : Fin 2) (n k m j : ℕ)
    (input : KoornwinderMeasureInput ρ μ ν := by
      first
        | assumption
        | exact KoornwinderMeasureInput.ofContinuous _ _ (by fun_prop)
        | (apply KoornwinderMeasureInput.ofMoments
           · aesop (rule_sets := [PolynomialIntegrability])
           · fun_prop))
    (hi : Integrable (fun v => eval v (X coord*S.polynomial n k) * eval v (S.polynomial m j))
      (koornwinderMeasure ρ μ ν) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) : ℝ :=
  integralInner (koornwinderMeasure ρ μ ν) (IntegrablePair.of (koornwinderMeasure ρ μ ν) (X coord*S.polynomial n k) (S.polynomial m j))

/-- Multiplication by a real coordinate has symmetric coefficients. -/
theorem multiplicationEntry_symm (coord : Fin 2) (n k m j : ℕ)
    (input : KoornwinderMeasureInput ρ μ ν := by
      first
        | assumption
        | exact KoornwinderMeasureInput.ofContinuous _ _ (by fun_prop)
        | (apply KoornwinderMeasureInput.ofMoments
           · aesop (rule_sets := [PolynomialIntegrability])
           · fun_prop))
    (hi : Integrable (fun v => eval v (X coord*S.polynomial n k) * eval v (S.polynomial m j))
      (koornwinderMeasure ρ μ ν) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    S.multiplicationEntry coord n k m j = S.multiplicationEntry coord m j n k (hi := by
      apply hi.congr
      exact Filter.Eventually.of_forall (fun v => by simp only [map_mul]; ring)) := by
  simp only [multiplicationEntry, integralInner, map_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by ring)

variable [SFinite μ] [SFinite ν] (hρ : Continuous ρ)
include hρ

/-- The x pairing leaves the inner factor unchanged. -/
theorem multiplicationEntry_x (n k m j : ℕ)
    (hi : Integrable (fun v => eval v (X 0*S.polynomial n k) * eval v (S.polynomial m j))
      (koornwinderMeasure ρ μ ν) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    S.multiplicationEntry 0 n k m j =
      (∫ x : D, (x : ℝ)*(S.outer k (n-k)).eval (x : ℝ)*(S.outer j (m-j)).eval (x : ℝ)*ρ x^(k+j) ∂μ) *
        Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (S.inner k) (S.inner j) (h := S.inner_orthogonal.integrable k j)) := by
  have he := (koornwinderMeasure_integral
    (KoornwinderMeasureInput.ofContinuous μ ν hρ)
    ⟨fun v ↦ eval v ((X 0*S.polynomial n k)*S.polynomial m j), by simpa only [map_mul] using hi⟩).2
  simp only [map_mul, eval_X] at he
  rw [multiplicationEntry, integralInner]
  simp only [map_mul, eval_X]
  rw [he, Polynomial.integralInner, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (S.eval_polynomial n k),
    Measure.quasiMeasurePreserving_fst.ae (S.eval_polynomial m j)] with v hv hw
  rw [hv v.2, hw v.2, pow_add]
  simp only [koornwinderCoordinates, Matrix.cons_val_zero]
  ring

/-- The y pairing shifts one power of the radius to the outer factor. -/
theorem multiplicationEntry_y (n k m j : ℕ)
    (hi : Integrable (fun v => eval v (X 1*S.polynomial n k) * eval v (S.polynomial m j))
      (koornwinderMeasure ρ μ ν) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    S.multiplicationEntry 1 n k m j =
      (∫ x : D, (S.outer k (n-k)).eval (x : ℝ)*(S.outer j (m-j)).eval (x : ℝ)*ρ x^(k+j+1) ∂μ) *
        Polynomial.integralInner ν (Polynomial.IntegrablePair.of ν (Polynomial.X*S.inner k) (S.inner j)
          (h := S.inner_orthogonal.hasFiniteMoments.integrable_mul _ _)) := by
  have he := (koornwinderMeasure_integral
    (KoornwinderMeasureInput.ofContinuous μ ν hρ)
    ⟨fun v ↦ eval v ((X 1*S.polynomial n k)*S.polynomial m j), by simpa only [map_mul] using hi⟩).2
  simp only [map_mul, eval_X] at he
  rw [multiplicationEntry, integralInner]
  simp only [map_mul, eval_X]
  rw [he, Polynomial.integralInner, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (S.eval_polynomial n k),
    Measure.quasiMeasurePreserving_fst.ae (S.eval_polynomial m j)] with v hv hw
  rw [hv v.2, hw v.2, pow_add, pow_add]
  simp only [koornwinderCoordinates, Matrix.cons_val_one, Matrix.cons_val_zero,
    Polynomial.eval_mul, Polynomial.eval_X,
    pow_one]
  ring

/-- The inner index in y multiplication has bandwidth one, for arbitrary scale degree. -/
theorem multiplicationEntry_y_eq_zero_of_inner_band (hν : Polynomial.HasFiniteMoments ν)
    {n k m j : ℕ} (hkj : k+1 < j ∨ j+1 < k)
    (hi : Integrable (fun v => eval v (X 1*S.polynomial n k) * eval v (S.polynomial m j))
      (koornwinderMeasure ρ μ ν) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) : S.multiplicationEntry 1 n k m j = 0 := by
  rw [S.multiplicationEntry_y hρ n k m j (hi := hi),
    S.inner_orthogonal.integralInner_X_mul_eq_zero hν hkj, mul_zero]

end MvPolynomial.KoornwinderSystem
