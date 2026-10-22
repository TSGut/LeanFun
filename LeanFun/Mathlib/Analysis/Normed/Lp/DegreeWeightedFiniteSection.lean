/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Lp.DegreeWeightedOperators
public import LeanFun.Mathlib.Analysis.Normed.Operator.FiniteSection

/-! # Stable finite systems on degree-weighted coefficient space
The abstract compact-perturbation theorem gives unique finite coefficient
systems and convergence in the square-summable norm.
Reference: Olver--Townsend (2013), Lemma 4.4 and Theorem 4.5.
-/

public section
namespace lp
variable (s : ℕ)
open Filter ContinuousLinearMap
open scoped Topology

/-- Weighted truncation is idempotent. -/
theorem degreeWeightedProjection_idempotent (n : ℕ) :
    (degreeWeightedProjection s n).comp (degreeWeightedProjection s n) =
      degreeWeightedProjection s n := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  funext i
  simp only [comp_apply, degreeWeightedProjection_apply]
  split_ifs <;> rfl

/-- Fixed points of the coordinate projection are exactly the supported vectors. -/
theorem degreeWeightedProjection_eq_self_iff (n : ℕ) (x : DegreeWeightedL2 s) :
    degreeWeightedProjection s n x = x ↔ ∀ i, n ≤ i → x.1 i = 0 := by
  constructor
  · intro h i hi
    have he := congrArg (fun v : DegreeWeightedL2 s ↦ v.1 i) h
    simpa [degreeWeightedProjection_apply, Nat.not_lt.mpr hi] using he.symm
  · intro h
    apply Subtype.ext
    funext i
    by_cases hi : i < n
    · simp [hi]
    · simp [hi, h i (by omega)]

/-- Projected equations compare exactly the first n coordinates. -/
theorem degreeWeightedProjection_eq_iff (n : ℕ) (x y : DegreeWeightedL2 s) :
    degreeWeightedProjection s n x = degreeWeightedProjection s n y ↔ ∀ i < n, x.1 i = y.1 i := by
  constructor
  · intro h i hi
    have he := congrArg (fun v : DegreeWeightedL2 s ↦ v.1 i) h
    simpa [hi] using he
  · intro h
    apply Subtype.ext
    funext i
    by_cases hi : i < n <;> simp [hi, h]

/-- An invertible compact perturbation has unique leading finite coefficient
systems for every sufficiently large size and every right-hand side. -/
theorem eventually_existsUnique_degreeWeighted_system
    (K : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s)
    (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    ∀ᶠ n in atTop, ∀ f : DegreeWeightedL2 s, ∃! x : DegreeWeightedL2 s,
      (∀ i, n ≤ i → x.1 i = 0) ∧ (∀ i < n, ((1 + K) x).1 i = f.1 i) := by
  filter_upwards [eventually_stable_liftedFiniteSection (degreeWeightedProjection s)
    (norm_degreeWeightedProjection_le s) (tendsto_degreeWeightedProjection s) K hK hT] with n hn f
  simpa only [degreeWeightedProjection_eq_self_iff, degreeWeightedProjection_eq_iff] using
    existsUnique_projected_solution (degreeWeightedProjection s n) K
      (degreeWeightedProjection_idempotent s n) hn.1 f

set_option maxHeartbeats 800000 in
/-- The coefficient error is bounded by a constant times the exact coefficient tail. -/
theorem eventually_degreeWeighted_system_error_le
    (K : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s)
    (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (liftedFiniteSection (degreeWeightedProjection s n) K),
      ∀ x : DegreeWeightedL2 s,
        ‖Ring.inverseAt (fun n ↦ liftedFiniteSection (degreeWeightedProjection s n) K) ⟨n, hn⟩
            (degreeWeightedProjection s n ((1 + K) x)) - x‖ ≤
          (‖(↑(hT.unit⁻¹) : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s)‖ + 1) *
            ‖degreeWeightedProjection s n x - x‖ :=
  eventually_norm_liftedFiniteSection_error_le (degreeWeightedProjection s)
    (norm_degreeWeightedProjection_le s) (tendsto_degreeWeightedProjection s) K hK hT

/-- Unique finite coefficient solves converge in the coefficient-space norm. -/
theorem tendsto_degreeWeighted_system_solution
    (K : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s)
    (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) (x : DegreeWeightedL2 s) :
    Tendsto (fun n : Ring.InvertibleIndex (fun n ↦ liftedFiniteSection (degreeWeightedProjection s n) K) ↦
      Ring.inverseAt (fun n ↦ liftedFiniteSection (degreeWeightedProjection s n) K) n
        (degreeWeightedProjection s n ((1 + K) x)))
      (Ring.invertibleIndexFilter (fun n ↦ liftedFiniteSection (degreeWeightedProjection s n) K) atTop)
      (𝓝 x) :=
  tendsto_liftedFiniteSection_solution (degreeWeightedProjection s)
    (norm_degreeWeightedProjection_le s) (tendsto_degreeWeightedProjection s) K hK hT x

/-- The domain of actual finite solves is cofinal and has a nontrivial limit filter. -/
theorem degreeWeighted_system_filter_neBot
    (K : DegreeWeightedL2 s →L[ℂ] DegreeWeightedL2 s)
    (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    NeBot (Ring.invertibleIndexFilter
      (fun n ↦ liftedFiniteSection (degreeWeightedProjection s n) K) atTop) :=
  invertible_liftedFiniteSection_filter_neBot (degreeWeightedProjection s)
    (norm_degreeWeightedProjection_le s) (tendsto_degreeWeightedProjection s) K hK hT

end lp
