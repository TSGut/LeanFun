/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Coordinate operators on square-summable coefficients
Coordinate truncations and diagonal multipliers use Mathlib's existing `lp`.
Reference: Olver--Townsend (2013), Section 4.
-/

@[expose] public section
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]
open Filter
open scoped Topology ENNReal

private theorem evalCLM_scalar_apply (i : ℕ) (x : lp (fun _ : ℕ ↦ 𝕜) 2) :
    evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i x = x i := rfl

/-- Projection onto the first n coordinates of real or complex square-summable sequences. -/
noncomputable def coefficientProjection (n : ℕ) :
    lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 :=
  ∑ i ∈ Finset.range n,
    (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i).comp (evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i)

/-- Coordinate truncation has the expected entries. -/
@[simp] theorem coefficientProjection_apply (n : ℕ) (x : lp (fun _ : ℕ ↦ 𝕜) 2) (i : ℕ) :
    coefficientProjection n x i = if i < n then x i else 0 := by
  classical
  simp only [coefficientProjection, sum_apply, ContinuousLinearMap.comp_apply,
    singleContinuousLinearMap_apply, evalCLM_scalar_apply, coeFn_sum, lp.coeFn_single,
    Finset.sum_apply, Finset.sum_pi_single, Finset.mem_range]


/-- Coordinate projections are contractions. -/
theorem norm_coefficientProjection_le (n : ℕ) : ‖coefficientProjection (𝕜 := 𝕜) n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  simp only [coefficientProjection_apply]
  split_ifs <;> simp

/-- A coordinate truncation is a projection. -/
theorem coefficientProjection_idempotent (n : ℕ) :
    (coefficientProjection (𝕜 := 𝕜) n).comp (coefficientProjection n) = coefficientProjection n := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, coefficientProjection_apply]
  split_ifs <;> rfl

/-- Coordinate truncations converge strongly to the identity. -/
theorem tendsto_coefficientProjection (x : lp (fun _ : ℕ ↦ 𝕜) 2) :
    Tendsto (fun n ↦ coefficientProjection n x) atTop (𝓝 x) := by
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat
  simpa only [coefficientProjection, sum_apply,
    ContinuousLinearMap.comp_apply, singleContinuousLinearMap_apply, evalCLM_scalar_apply] using h

/-- Coordinate truncations have compact finite-dimensional range. -/
theorem isCompactOperator_coefficientProjection (n : ℕ) :
    IsCompactOperator (coefficientProjection (𝕜 := 𝕜) n) := by
  classical
  have h (s : Finset ℕ) : IsCompactOperator
      (∑ i ∈ s, (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i).comp
        (evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i) :
        lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2))
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((isCompactOperator_of_locallyCompactSpace_rng
        (singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i)).comp_clm
          (evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 i)).add ih
  exact h _

/-- A uniformly bounded diagonal coefficient multiplier. -/
noncomputable def coefficientDiagonal (d : ℕ → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, ‖d i‖ ≤ C) : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 :=
  mapCLM 2 (fun i ↦ d i • ContinuousLinearMap.id 𝕜 𝕜) hC (fun i ↦ by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hd i)

/-- A diagonal multiplier acts coordinatewise. -/
@[simp] theorem coefficientDiagonal_apply (d : ℕ → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, ‖d i‖ ≤ C) (x : lp (fun _ : ℕ ↦ 𝕜) 2) (i : ℕ) :
    coefficientDiagonal d hC hd x i = d i * x i := rfl

/-- The operator norm is bounded by a uniform diagonal bound. -/
theorem norm_coefficientDiagonal_le (d : ℕ → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, ‖d i‖ ≤ C) : ‖coefficientDiagonal d hC hd‖ ≤ C :=
  norm_mapCLM_le ..

/-- A diagonal tail is bounded in norm by a uniform bound on its remaining entries. -/
theorem norm_coefficientDiagonal_tail_le (d : ℕ → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, ‖d i‖ ≤ C) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (ht : ∀ i, n ≤ i → ‖d i‖ ≤ ε) :
    ‖coefficientDiagonal d hC hd - (coefficientProjection n).comp
      (coefficientDiagonal d hC hd)‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro x
  calc
    _ ≤ ‖ε • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      simp only [sub_apply, ContinuousLinearMap.comp_apply,
        coeFn_sub, Pi.sub_apply, coefficientDiagonal_apply, coefficientProjection_apply,
        coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
      split_ifs with hi
      · simpa using mul_nonneg hε (norm_nonneg (x i))
      · simpa only [sub_zero, norm_mul] using
          mul_le_mul_of_nonneg_right (ht i (by omega)) (norm_nonneg (x i))
    _ = ε * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]

/-- A diagonal tending to zero is the norm limit of its finite coordinate sections. -/
theorem tendsto_coefficientDiagonal_sections (d : ℕ → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, ‖d i‖ ≤ C) (hlim : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n ↦ (coefficientProjection n).comp (coefficientDiagonal d hC hd))
      atTop (𝓝 (coefficientDiagonal d hC hd)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  apply lt_of_le_of_lt (norm_coefficientDiagonal_tail_le d hC hd n (by positivity)
    (fun i hi ↦ ?_)) (by linarith : ε / 2 < ε)
  simpa only [dist_zero_right] using (hN i (hn.trans hi)).le

/-- Diagonal decay implies compactness on coefficient space. -/
theorem isCompactOperator_coefficientDiagonal (d : ℕ → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, ‖d i‖ ≤ C) (hlim : Tendsto d atTop (𝓝 0)) :
    IsCompactOperator (coefficientDiagonal d hC hd) :=
  isCompactOperator_of_tendsto (tendsto_coefficientDiagonal_sections d hC hd hlim)
    (Eventually.of_forall (fun n ↦ (isCompactOperator_coefficientProjection n).comp_clm _))

end lp
