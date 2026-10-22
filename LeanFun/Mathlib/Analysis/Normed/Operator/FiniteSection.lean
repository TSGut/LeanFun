/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Ring.IndexedInverse
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-! # Stable finite sections of compact perturbations
Strongly convergent uniformly bounded projections converge in operator norm
when composed with a compact operator. Inversion then gives stable finite
sections. Reference: Olver--Townsend (2013), Lemma 4.4 and Theorem 4.5.
-/

public section
namespace ContinuousLinearMap
open Filter Set
open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Uniformly bounded operators converging strongly to the identity converge
uniformly on compact sets. -/
theorem tendstoUniformlyOn_of_strongly_tendsto_id
    (P : ℕ → E →L[𝕜] E) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    {S : Set E} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n x ↦ P n x) id atTop S := by
  have he : UniformEquicontinuous (fun n x ↦ P n x) :=
    Metric.uniformEquicontinuous_of_continuity_modulus (fun t ↦ C * t)
      (by simpa using (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).const_mul C) _ (fun x y n ↦ by
        simpa only [dist_eq_norm, ← map_sub] using
          (P n).le_opNorm (x - y) |>.trans
            (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)))
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (((equicontinuous_restrict_iff _).mpr (he.equicontinuous.equicontinuousOn S)).tendsto_uniformFun_iff_pi
    atTop (fun x : S ↦ (x : E))).2
  exact tendsto_pi_nhds.mpr (fun x ↦ hP x)

/-- Strong convergence of uniformly bounded operators becomes norm convergence
after composition on the right with a compact operator. -/
theorem tendsto_compact_comp_of_strongly_tendsto_id
    (P : ℕ → E →L[𝕜] E) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) :
    Tendsto (fun n ↦ (P n).comp K) atTop (𝓝 K) := by
  obtain ⟨S, hS, hKS⟩ := hK.image_closedBall_subset_compact (f := K.toLinearMap) 1
  have h := tendstoUniformlyOn_of_strongly_tendsto_id P hC hP hS
  rw [Metric.tendstoUniformlyOn_iff] at h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (ε / 2) (by positivity))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := ε / 2) _ (by linarith)
  apply opNorm_le_of_unit_norm (by positivity)
  intro x hx
  have hxs : K x ∈ S := hKS ⟨x, by simp [Metric.mem_closedBall, dist_zero_right, hx], rfl⟩
  have ht := (hN n hn (K x) hxs).le
  simpa only [id_eq, dist_eq_norm, norm_sub_rev, sub_apply, comp_apply] using ht

variable [CompleteSpace E]

/-- Invertible norm limits have eventually invertible approximants. -/
theorem eventually_isUnit_of_tendsto {A : ℕ → E →L[𝕜] E} {T : E →L[𝕜] E}
    (hA : Tendsto A atTop (𝓝 T)) (hT : IsUnit T) :
    ∀ᶠ n in atTop, IsUnit (A n) :=
  hA (Units.isOpen.mem_nhds hT)

/-- Inverses of norm-convergent invertible approximants converge in norm. -/
theorem tendsto_inverse_of_tendsto {A : ℕ → E →L[𝕜] E} {T : E →L[𝕜] E}
    (hA : Tendsto A atTop (𝓝 T)) (hT : IsUnit T) :
    Tendsto (fun n ↦ Ring.inverse (A n)) atTop (𝓝 (Ring.inverse T)) := by
  obtain ⟨u, rfl⟩ := hT
  exact (NormedRing.inverse_continuousAt u).tendsto.comp hA

/-- Inverse norms admit an eventual bound independent of the section size. -/
theorem eventually_norm_inverse_le_of_tendsto {A : ℕ → E →L[𝕜] E} {T : E →L[𝕜] E}
    (hA : Tendsto A atTop (𝓝 T)) (hT : IsUnit T) :
    ∀ᶠ n in atTop, ‖Ring.inverse (A n)‖ ≤ ‖Ring.inverse T‖ + 1 := by
  have h := (tendsto_inverse_of_tendsto hA hT).norm
  filter_upwards [h (gt_mem_nhds (lt_add_one ‖Ring.inverse T‖))] with n hn
  exact hn.le

/-- Lift a projected equation to the whole space by retaining the identity on
unresolved coordinates. Its restriction to a projection range is the finite section. -/
@[expose] noncomputable def liftedFiniteSection (P K : E →L[𝕜] E) : E →L[𝕜] E :=
  1 + P.comp K

omit [CompleteSpace E] in
/-- Compactness gives operator-norm convergence of the lifted sections. -/
theorem tendsto_liftedFiniteSection (P : ℕ → E →L[𝕜] E) {C : ℝ}
    (hC : ∀ n, ‖P n‖ ≤ C) (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) :
    Tendsto (fun n ↦ liftedFiniteSection (P n) K) atTop (𝓝 (1 + K)) :=
  tendsto_const_nhds.add (tendsto_compact_comp_of_strongly_tendsto_id P hC hP K hK)

/-- Invertibility and a uniform inverse bound hold for every sufficiently large section. -/
theorem eventually_stable_liftedFiniteSection_ringInverse (P : ℕ → E →L[𝕜] E) {C : ℝ}
    (hC : ∀ n, ‖P n‖ ≤ C) (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    ∀ᶠ n in atTop, IsUnit (liftedFiniteSection (P n) K) ∧
      ‖Ring.inverse (liftedFiniteSection (P n) K)‖ ≤ ‖Ring.inverse (1 + K)‖ + 1 := by
  have h := tendsto_liftedFiniteSection P hC hP K hK
  exact (eventually_isUnit_of_tendsto h hT).and (eventually_norm_inverse_le_of_tendsto h hT)

omit [CompleteSpace E] in
/-- The lifted inverse solution is genuinely in the projection range and
solves the projected equation. -/
theorem liftedFiniteSection_solution_mem (P K : E →L[𝕜] E)
    (hP : P.comp P = P) (hA : IsUnit (liftedFiniteSection P K)) (f : E) :
    let x := Ring.inverse (liftedFiniteSection P K) (P f)
    P x = x ∧ P ((1 + K) x) = P f := by
  let x := Ring.inverse (liftedFiniteSection P K) (P f)
  change P x = x ∧ P ((1 + K) x) = P f
  have hx : x + P (K x) = P f := by
    have h := congrArg (fun T : E →L[𝕜] E ↦ T (P f))
      (Ring.mul_inverse_cancel (liftedFiniteSection P K) hA)
    simpa only [x, mul_apply_eq_comp, liftedFiniteSection, add_apply, one_apply_eq_self, comp_apply] using h
  have hp (y : E) : P (P y) = P y := congrArg (fun T : E →L[𝕜] E ↦ T y) hP
  have hxP : P x = x := by
    have hh := congrArg P hx
    rw [map_add, hp, hp, ← hx] at hh
    exact add_right_cancel hh
  exact ⟨hxP, by simpa only [add_apply, one_apply_eq_self, map_add, hxP] using hx⟩

omit [CompleteSpace E] in
/-- The section error is the lifted inverse applied to the original projection tail. -/
theorem liftedFiniteSection_error_eq (P K : E →L[𝕜] E)
    (hA : IsUnit (liftedFiniteSection P K)) (x : E) :
    Ring.inverse (liftedFiniteSection P K) (P ((1 + K) x)) - x =
      Ring.inverse (liftedFiniteSection P K) (P x - x) := by
  have hx : Ring.inverse (liftedFiniteSection P K) (liftedFiniteSection P K x) = x := by
    have h := congrArg (fun T : E →L[𝕜] E ↦ T x)
      (Ring.inverse_mul_cancel (liftedFiniteSection P K) hA)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  calc
    _ = Ring.inverse (liftedFiniteSection P K) (P ((1 + K) x)) -
        Ring.inverse (liftedFiniteSection P K) (liftedFiniteSection P K x) := by rw [hx]
    _ = Ring.inverse (liftedFiniteSection P K)
        (P ((1 + K) x) - liftedFiniteSection P K x) := (map_sub _ _ _).symm
    _ = _ := by
      congr 1
      simp only [liftedFiniteSection, add_apply, one_apply_eq_self, comp_apply, map_add]
      abel

/-- Quasioptimality: discrete solution error is bounded by a section-independent
constant times the exact solution's projection tail. -/
theorem eventually_norm_liftedFiniteSection_error_le_ringInverse
    (P : ℕ → E →L[𝕜] E) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    ∀ᶠ n in atTop, ∀ x : E,
      ‖Ring.inverse (liftedFiniteSection (P n) K) (P n ((1 + K) x)) - x‖ ≤
        (‖Ring.inverse (1 + K)‖ + 1) * ‖P n x - x‖ := by
  filter_upwards [eventually_stable_liftedFiniteSection_ringInverse P hC hP K hK hT] with n hn x
  rw [liftedFiniteSection_error_eq _ _ hn.1]
  exact (Ring.inverse (liftedFiniteSection (P n) K)).le_opNorm _ |>.trans
    (mul_le_mul_of_nonneg_right hn.2 (norm_nonneg _))

/-- Finite-section solutions converge to the exact solution of an invertible
compact perturbation of the identity. -/
theorem tendsto_liftedFiniteSection_solution_ringInverse
    (P : ℕ → E →L[𝕜] E) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) (x : E) :
    Tendsto (fun n ↦ Ring.inverse (liftedFiniteSection (P n) K) (P n ((1 + K) x)))
      atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    ((eventually_norm_liftedFiniteSection_error_le_ringInverse P hC hP K hK hT).mono (fun _ h ↦ h x))
  simpa using ((hP x).sub (tendsto_const_nhds (x := x))).norm.const_mul (‖Ring.inverse (1 + K)‖ + 1)

omit [CompleteSpace E] in
/-- An invertible lifted section gives a unique solution of the actual
projected equations inside the projection range. -/
theorem existsUnique_projected_solution (P K : E →L[𝕜] E)
    (hP : P.comp P = P) (hA : IsUnit (liftedFiniteSection P K)) (f : E) :
    ∃! x : E, P x = x ∧ P ((1 + K) x) = P f := by
  refine ⟨Ring.inverse (liftedFiniteSection P K) (P f),
    liftedFiniteSection_solution_mem P K hP hA f, ?_⟩
  intro y hy
  have he : liftedFiniteSection P K y = P f := by
    simpa only [liftedFiniteSection, add_apply, one_apply_eq_self, comp_apply,
      map_add, hy.1] using hy.2
  have hi := congrArg (fun T : E →L[𝕜] E ↦ T y)
    (Ring.inverse_mul_cancel (liftedFiniteSection P K) hA)
  simpa only [mul_apply_eq_comp, one_apply_eq_self, he] using hi.symm

end ContinuousLinearMap

namespace ContinuousLinearMap
open Filter Set
open scoped Topology
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The invertible-cutoff filter of compact perturbations is nontrivial. -/
theorem invertible_liftedFiniteSection_filter_neBot
    (P : ℕ → E →L[𝕜] E) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    NeBot (Ring.invertibleIndexFilter (fun n ↦ liftedFiniteSection (P n) K) atTop) := by
  exact Ring.invertibleIndexFilter_neBot _ _
    (eventually_isUnit_of_tendsto (tendsto_liftedFiniteSection P hC hP K hK) hT)

/-- Finite-section convergence uses only actual inverses. -/
theorem tendsto_liftedFiniteSection_solution
    (P : ℕ → E →L[𝕜] E) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) (x : E) :
    Tendsto (fun n : Ring.InvertibleIndex (fun n ↦ liftedFiniteSection (P n) K) ↦
      Ring.inverseAt (fun n ↦ liftedFiniteSection (P n) K) n (P n ((1 + K) x)))
      (Ring.invertibleIndexFilter (fun n ↦ liftedFiniteSection (P n) K) atTop)
      (𝓝 x) := by
  have h := (tendsto_liftedFiniteSection_solution_ringInverse P hC hP K hK hT x).comp
    (Filter.tendsto_comap : Tendsto
      (Subtype.val : Ring.InvertibleIndex (fun n ↦ liftedFiniteSection (P n) K) → ℕ)
      (Filter.comap Subtype.val atTop) atTop)
  simpa only [Ring.invertibleIndexFilter, Function.comp_def, Ring.inverseAt_eq_ringInverse] using h

/-- Stability provides actual inverse values for every sufficiently large cutoff. -/
theorem eventually_stable_liftedFiniteSection
    (P : ℕ → E →L[𝕜] E) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (liftedFiniteSection (P n) K),
      ‖Ring.inverseAt (fun n ↦ liftedFiniteSection (P n) K) ⟨n, hn⟩‖ ≤
        ‖(↑(hT.unit⁻¹) : E →L[𝕜] E)‖ + 1 := by
  filter_upwards [eventually_stable_liftedFiniteSection_ringInverse P hC hP K hK hT] with n hn
  refine ⟨hn.1, ?_⟩
  have hunit : Ring.inverse (1 + K) = (↑(hT.unit⁻¹) : E →L[𝕜] E) := by
    simpa only [IsUnit.unit_spec] using Ring.inverse_unit hT.unit
  simpa only [Ring.inverseAt_eq_ringInverse, hunit] using hn.2

/-- The classical finite-section error bound is asserted together with existence. -/
theorem eventually_norm_liftedFiniteSection_error_le
    (P : ℕ → E →L[𝕜] E) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hT : IsUnit (1 + K)) :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (liftedFiniteSection (P n) K), ∀ x : E,
      ‖Ring.inverseAt (fun n ↦ liftedFiniteSection (P n) K) ⟨n, hn⟩
          (P n ((1 + K) x)) - x‖ ≤
        (‖(↑(hT.unit⁻¹) : E →L[𝕜] E)‖ + 1) * ‖P n x - x‖ := by
  filter_upwards [eventually_stable_liftedFiniteSection_ringInverse P hC hP K hK hT,
    eventually_norm_liftedFiniteSection_error_le_ringInverse P hC hP K hK hT] with n hn he
  refine ⟨hn.1, fun x ↦ ?_⟩
  have hunit : Ring.inverse (1 + K) = (↑(hT.unit⁻¹) : E →L[𝕜] E) := by
    simpa only [IsUnit.unit_spec] using Ring.inverse_unit hT.unit
  simpa only [Ring.inverseAt_eq_ringInverse, hunit] using he x
end ContinuousLinearMap
