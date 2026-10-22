/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Lp.CoefficientOperators
public import LeanFun.Mathlib.Analysis.Normed.Operator.FiniteSection

/-! # Stable finite systems on coefficient space
The abstract compact-perturbation theorem gives unique finite coefficient
systems and convergence in the square-summable norm.
Reference: Olver--Townsend (2013), Lemma 4.4 and Theorem 4.5.
-/

public section
namespace lp
open Filter ContinuousLinearMap
open scoped Topology

/-- Fixed points of the coordinate projection are exactly the supported vectors. -/
theorem coefficientProjection_eq_self_iff (n : ℕ) (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    coefficientProjection n x = x ↔ ∀ i, n ≤ i → x i = 0 := by
  constructor
  · intro h i hi
    have he := congrArg (fun v : lp (fun _ : ℕ ↦ ℂ) 2 ↦ v i) h
    simpa [coefficientProjection_apply, Nat.not_lt.mpr hi] using he.symm
  · intro h
    ext i
    by_cases hi : i < n
    · simp [hi]
    · simp [hi, h i (by omega)]

/-- Projected equations compare exactly the first n coordinates. -/
theorem coefficientProjection_eq_iff (n : ℕ) (x y : lp (fun _ : ℕ ↦ ℂ) 2) :
    coefficientProjection n x = coefficientProjection n y ↔ ∀ i < n, x i = y i := by
  constructor
  · intro h i hi
    have he := congrArg (fun v : lp (fun _ : ℕ ↦ ℂ) 2 ↦ v i) h
    simpa [hi] using he
  · intro h
    ext i
    by_cases hi : i < n <;> simp [hi, h]

/-- An invertible compact perturbation has unique leading finite coefficient
systems for every sufficiently large size and every right-hand side. -/
theorem eventually_existsUnique_coefficient_system
    (K : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    ∀ᶠ n in atTop, ∀ f : lp (fun _ : ℕ ↦ ℂ) 2, ∃! x : lp (fun _ : ℕ ↦ ℂ) 2,
      (∀ i, n ≤ i → x i = 0) ∧ (∀ i < n, ((1 + K) x) i = f i) := by
  filter_upwards [eventually_stable_liftedFiniteSection (coefficientProjection (𝕜 := ℂ))
    (norm_coefficientProjection_le (𝕜 := ℂ)) (tendsto_coefficientProjection (𝕜 := ℂ)) K hK hT] with n hn f
  simpa only [coefficientProjection_eq_self_iff, coefficientProjection_eq_iff] using
    existsUnique_projected_solution (coefficientProjection n) K
      (coefficientProjection_idempotent n) hn.1 f

set_option maxHeartbeats 800000 in
/-- The coefficient error is bounded by a constant times the exact coefficient tail. -/
theorem eventually_coefficient_system_error_le
    (K : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (liftedFiniteSection (coefficientProjection n) K),
      ∀ x : lp (fun _ : ℕ ↦ ℂ) 2,
        ‖Ring.inverseAt (fun n ↦ liftedFiniteSection (coefficientProjection n) K) ⟨n, hn⟩
            (coefficientProjection n ((1 + K) x)) - x‖ ≤
          (‖(↑(hT.unit⁻¹) : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)‖ + 1) *
            ‖coefficientProjection n x - x‖ :=
  eventually_norm_liftedFiniteSection_error_le (coefficientProjection (𝕜 := ℂ))
    (norm_coefficientProjection_le (𝕜 := ℂ)) (tendsto_coefficientProjection (𝕜 := ℂ)) K hK hT

/-- Unique finite coefficient solves converge in the coefficient-space norm. -/
theorem tendsto_coefficient_system_solution
    (K : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) (x : lp (fun _ : ℕ ↦ ℂ) 2) :
    Tendsto (fun n : Ring.InvertibleIndex (fun n ↦ liftedFiniteSection (coefficientProjection n) K) ↦
      Ring.inverseAt (fun n ↦ liftedFiniteSection (coefficientProjection n) K) n
        (coefficientProjection n ((1 + K) x)))
      (Ring.invertibleIndexFilter (fun n ↦ liftedFiniteSection (coefficientProjection n) K) atTop)
      (𝓝 x) :=
  tendsto_liftedFiniteSection_solution (coefficientProjection (𝕜 := ℂ))
    (norm_coefficientProjection_le (𝕜 := ℂ)) (tendsto_coefficientProjection (𝕜 := ℂ)) K hK hT x

/-- The domain of actual finite solves is cofinal and has a nontrivial limit filter. -/
theorem coefficient_system_filter_neBot
    (K : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
    (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    NeBot (Ring.invertibleIndexFilter
      (fun n ↦ liftedFiniteSection (coefficientProjection n) K) atTop) :=
  invertible_liftedFiniteSection_filter_neBot (coefficientProjection (𝕜 := ℂ))
    (norm_coefficientProjection_le (𝕜 := ℂ)) (tendsto_coefficientProjection (𝕜 := ℂ)) K hK hT

end lp
