/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Operator.FiniteSection

/-! # Finite sections with approximate operators

Norm-consistent operator approximations preserve finite-section stability.
The error separates the solution's projection tail and the operator error.
Reference: the compact-perturbation argument of Olver–Townsend (2013), §4.
-/

public section
namespace ContinuousLinearMap
open Filter
open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Contractive sections remain norm-consistent when the compact operator is
itself approximated in norm. -/
theorem tendsto_approximateLiftedFiniteSection
    (P : ℕ → E →L[𝕜] E) (hC : ∀ n, ‖P n‖ ≤ 1)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K)
    (L : ℕ → E →L[𝕜] E) (hL : Tendsto L atTop (𝓝 K)) :
    Tendsto (fun n ↦ liftedFiniteSection (P n) (L n)) atTop (𝓝 (1 + K)) := by
  have he : Tendsto (fun n ↦ (P n).comp (L n - K)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ ?_) (by
      simpa using (hL.sub (tendsto_const_nhds (x := K))).norm)
    exact (opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hC n) (norm_nonneg (L n - K)))
  have ht := (tendsto_liftedFiniteSection P hC hP K hK).add he
  simpa only [liftedFiniteSection, comp_sub, add_sub_cancel_right, add_zero,
    add_add_sub_cancel] using ht

/-- Exact error identity with both projection and operator approximation errors. -/
theorem approximateLiftedFiniteSection_error_eq_ringInverse (P K L : E →L[𝕜] E)
    (hA : IsUnit (liftedFiniteSection P L)) (x : E) :
    Ring.inverse (liftedFiniteSection P L) (P ((1 + K) x)) - x =
      Ring.inverse (liftedFiniteSection P L) (P x - x + P ((K - L) x)) := by
  have hx : Ring.inverse (liftedFiniteSection P L) (liftedFiniteSection P L x) = x := by
    have h := congrArg (fun T : E →L[𝕜] E ↦ T x)
      (Ring.inverse_mul_cancel (liftedFiniteSection P L) hA)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  calc
    _ = Ring.inverse (liftedFiniteSection P L)
        (P ((1 + K) x) - liftedFiniteSection P L x) := by rw [map_sub, hx]
    _ = _ := by
      congr 1
      simp only [liftedFiniteSection, add_apply, sub_apply, one_apply_eq_self,
        comp_apply, map_add, map_sub]
      abel

/-- A contractive projection gives the sum of a projection-tail error and an
operator consistency error, multiplied by the discrete inverse norm. -/
theorem norm_approximateLiftedFiniteSection_error_le_ringInverse (P K L : E →L[𝕜] E)
    (hP : ‖P‖ ≤ 1) (hA : IsUnit (liftedFiniteSection P L)) (x : E) :
    ‖Ring.inverse (liftedFiniteSection P L) (P ((1 + K) x)) - x‖ ≤
      ‖Ring.inverse (liftedFiniteSection P L)‖ * (‖P x - x‖ + ‖K - L‖ * ‖x‖) := by
  rw [approximateLiftedFiniteSection_error_eq_ringInverse P K L hA]
  refine ((Ring.inverse (liftedFiniteSection P L)).le_opNorm _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  calc
    ‖P ((K - L) x)‖ ≤ ‖(K - L) x‖ := (P.le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg ((K - L) x)))
    _ ≤ ‖K - L‖ * ‖x‖ := (K - L).le_opNorm x


/-- Classical error identity on the exact domain of invertible lifted sections. -/
theorem approximateLiftedFiniteSection_error_eq (P K : E →L[𝕜] E)
    (L : Ring.InvertibleIndex (liftedFiniteSection P)) (x : E) :
    Ring.inverseAt (liftedFiniteSection P) L (P ((1 + K) x)) - x =
      Ring.inverseAt (liftedFiniteSection P) L (P x - x + P ((K - L.val) x)) := by
  simpa only [Ring.inverseAt_eq_ringInverse] using
    approximateLiftedFiniteSection_error_eq_ringInverse P K L.val L.property x

/-- Classical projection-tail and operator-error estimate. -/
theorem norm_approximateLiftedFiniteSection_error_le (P K : E →L[𝕜] E)
    (L : Ring.InvertibleIndex (liftedFiniteSection P)) (hP : ‖P‖ ≤ 1) (x : E) :
    ‖Ring.inverseAt (liftedFiniteSection P) L (P ((1 + K) x)) - x‖ ≤
      ‖Ring.inverseAt (liftedFiniteSection P) L‖ * (‖P x - x‖ + ‖K - L.val‖ * ‖x‖) := by
  simpa only [Ring.inverseAt_eq_ringInverse] using
    norm_approximateLiftedFiniteSection_error_le_ringInverse P K L.val hP L.property x

variable [CompleteSpace E]

/-- Simultaneously refined operator approximations and sections are eventually
invertible with a bound depending only on the limiting inverse. -/
theorem eventually_stable_approximateLiftedFiniteSection_ringInverse
    (P : ℕ → E →L[𝕜] E) (hC : ∀ n, ‖P n‖ ≤ 1)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K))
    (L : ℕ → E →L[𝕜] E) (hL : Tendsto L atTop (𝓝 K)) :
    ∀ᶠ n in atTop, IsUnit (liftedFiniteSection (P n) (L n)) ∧
      ‖Ring.inverse (liftedFiniteSection (P n) (L n))‖ ≤ ‖Ring.inverse (1 + K)‖ + 1 := by
  have h := tendsto_approximateLiftedFiniteSection P hC hP K hK L hL
  exact (eventually_isUnit_of_tendsto h hT).and (eventually_norm_inverse_le_of_tendsto h hT)


/-- Approximate-section stability supplies actual inverse values. -/
theorem eventually_stable_approximateLiftedFiniteSection
    (P : ℕ → E →L[𝕜] E) (hC : ∀ n, ‖P n‖ ≤ 1)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K))
    (L : ℕ → E →L[𝕜] E) (hL : Tendsto L atTop (𝓝 K)) :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (liftedFiniteSection (P n) (L n)),
      ‖Ring.inverseAt (fun n ↦ liftedFiniteSection (P n) (L n)) ⟨n, hn⟩‖ ≤
        ‖(↑(hT.unit⁻¹) : E →L[𝕜] E)‖ + 1 := by
  filter_upwards [eventually_stable_approximateLiftedFiniteSection_ringInverse P hC hP K hK hT L hL]
    with n hn
  refine ⟨hn.1, ?_⟩
  have hunit : Ring.inverse (1 + K) = (↑(hT.unit⁻¹) : E →L[𝕜] E) := by
    simpa only [IsUnit.unit_spec] using Ring.inverse_unit hT.unit
  simpa only [Ring.inverseAt_eq_ringInverse, hunit] using hn.2

/-- Norm-consistent sections have a nontrivial invertible-cutoff filter. -/
theorem approximateLiftedFiniteSection_filter_neBot
    (P : ℕ → E →L[𝕜] E) (hC : ∀ n, ‖P n‖ ≤ 1)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K))
    (L : ℕ → E →L[𝕜] E) (hL : Tendsto L atTop (𝓝 K)) :
    NeBot (Ring.invertibleIndexFilter (fun n ↦ liftedFiniteSection (P n) (L n)) atTop) :=
  Ring.invertibleIndexFilter_neBot _ _
    ((eventually_stable_approximateLiftedFiniteSection_ringInverse P hC hP K hK hT L hL).mono
      (fun _ h ↦ h.1))

end ContinuousLinearMap
