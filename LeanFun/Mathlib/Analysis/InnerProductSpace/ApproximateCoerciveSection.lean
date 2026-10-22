/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.CoerciveSections
public import LeanFun.Mathlib.Analysis.Normed.Operator.NormPerturbation

/-! # Double finite sections with approximate operators and data

Reference: Banach perturbation lemma and the finite-section method of
Böttcher–Silbermann. Stability of the reference sections is explicit.
-/

public noncomputable section
open ContinuousLinearMap Filter
open scoped Topology
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]
local notation "H" => lp (fun _ : ℕ ↦ 𝕜) 2

/-- Double compression does not amplify operator approximation error. -/
theorem norm_coerciveFiniteSection_sub_le (N : ℕ) (A B : H →L[𝕜] H) :
    ‖coerciveFiniteSection (initialL2Projection N) A -
      coerciveFiniteSection (initialL2Projection N) B‖ ≤ ‖A-B‖ := by
  have he : coerciveFiniteSection (initialL2Projection N) A -
      coerciveFiniteSection (initialL2Projection N) B =
      (initialL2Projection N).comp ((A-B).comp (initialL2Projection N)) := by
    simp only [coerciveFiniteSection, sub_comp, comp_sub]
    abel
  rw [he]
  apply (opNorm_comp_le _ _).trans
  calc
    _ ≤ 1 * (‖A-B‖ * 1) := mul_le_mul (norm_initialL2Projection_le N)
      ((opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
        (norm_initialL2Projection_le N) (norm_nonneg _))) (norm_nonneg _) zero_le_one
    _ = _ := by ring

/-- Norm-consistent approximate operators have strongly consistent double sections. -/
theorem tendsto_approximateCoerciveFiniteSection (A : H →L[𝕜] H)
    (B : ℕ → H →L[𝕜] H) (hB : Tendsto B atTop (𝓝 A)) (u : H) :
    Tendsto (fun N ↦ coerciveFiniteSection (initialL2Projection N) (B N) u)
      atTop (𝓝 (A u)) := by
  have hc : Continuous (fun p : (H →L[𝕜] H) × H ↦ p.1 p.2) := by fun_prop
  have hinner : Tendsto (fun N ↦ B N (initialL2Projection N u)) atTop (𝓝 (A u)) :=
    hc.continuousAt.tendsto.comp (hB.prodMk_nhds (tendsto_initialL2Projection u))
  have houter := tendsto_apply_of_strongly_tendsto_of_tendsto
    (fun N ↦ initialL2Projection (𝕜 := 𝕜) N) 1 norm_initialL2Projection_le
    tendsto_initialL2Projection hinner
  change Tendsto (fun N ↦ u-initialL2Projection N u+
    initialL2Projection N (B N (initialL2Projection N u))) atTop (𝓝 (A u))
  simpa only [one_apply_eq_self, sub_self, zero_add] using
    ((tendsto_const_nhds (x := u)).sub (tendsto_initialL2Projection u)).add houter

/-- Norm-consistent approximate sections inherit eventual stability. -/
theorem eventually_stable_approximateCoerciveFiniteSection (A : H →L[𝕜] H)
    (B : ℕ → H →L[𝕜] H) (hB : Tendsto B atTop (𝓝 A)) {C : ℝ}
    (hA : ∀ᶠ N in atTop, IsUnit (coerciveFiniteSection (initialL2Projection N) A) ∧
      ‖Ring.inverse (coerciveFiniteSection (initialL2Projection N) A)‖ ≤ C) :
    ∀ᶠ N in atTop, IsUnit (coerciveFiniteSection (initialL2Projection N) (B N)) ∧
      ‖Ring.inverse (coerciveFiniteSection (initialL2Projection N) (B N))‖ ≤ 2*C := by
  apply eventually_stable_of_norm_sub_tendsto_zero _ _ hA
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun N ↦ norm_coerciveFiniteSection_sub_le N A (B N))
  simpa using ((tendsto_const_nhds (x := A)).sub hB).norm

/-- Operator approximation, data approximation and increasing cutoffs may be refined together. -/
theorem tendsto_approximateCoerciveFiniteSection_solution (A : H →L[𝕜] H)
    (B : ℕ → H →L[𝕜] H) (hB : Tendsto B atTop (𝓝 A)) {C : ℝ}
    (hA : ∀ᶠ N in atTop, IsUnit (coerciveFiniteSection (initialL2Projection N) A) ∧
      ‖Ring.inverse (coerciveFiniteSection (initialL2Projection N) A)‖ ≤ C)
    (u : H) (g : ℕ → H) (hg : Tendsto g atTop (𝓝 (A u))) :
    Tendsto (fun N ↦ Ring.inverse
      (coerciveFiniteSection (initialL2Projection N) (B N)) (initialL2Projection N (g N)))
      atTop (𝓝 u) := by
  apply tendsto_inverse_apply_of_eventually_stable _
    (eventually_stable_approximateCoerciveFiniteSection A B hB hA) u
  have hp := tendsto_apply_of_strongly_tendsto_of_tendsto
    (fun N ↦ initialL2Projection (𝕜 := 𝕜) N) 1 norm_initialL2Projection_le
    tendsto_initialL2Projection hg
  simpa only [one_apply_eq_self, sub_self] using
    hp.sub (tendsto_approximateCoerciveFiniteSection A B hB u)

/-- A finite solve separates truncation, data, and preconditioned operator errors. -/
theorem norm_approximateCoerciveFiniteSection_error_le
    (A B : H →L[𝕜] H) (N : ℕ) (u g : H)
    (hB : IsUnit (coerciveFiniteSection (initialL2Projection N) B)) :
    ‖Ring.inverse (coerciveFiniteSection (initialL2Projection N) B)
        (initialL2Projection N g)-u‖ ≤
      ‖Ring.inverse (coerciveFiniteSection (initialL2Projection N) B)‖ *
        ((1+‖A‖)*‖initialL2Projection N u-u‖ + ‖g-A u‖ + ‖A-B‖*‖u‖) := by
  let P := initialL2Projection (𝕜 := 𝕜) N
  have hp (v : H) : ‖P v‖ ≤ ‖v‖ := norm_initialL2Projection_apply_le N v
  have he : P g-coerciveFiniteSection P A u =
      (P u-u)+P (g-A u)+P (A (u-P u)) := by
    simp only [coerciveFiniteSection, add_apply, sub_apply, one_apply_eq_self,
      comp_apply, map_sub]
    abel
  have hb : ‖P g-coerciveFiniteSection P A u‖ ≤
      (1+‖A‖)*‖P u-u‖+‖g-A u‖ := by
    rw [he]
    have ht := norm_add_le ((P u-u)+P (g-A u)) (P (A (u-P u)))
    have hs := norm_add_le (P u-u) (P (g-A u))
    have hd := hp (g-A u)
    have ho := hp (A (u-P u))
    have ha := A.le_opNorm (u-P u)
    rw [norm_sub_rev u] at ha
    nlinarith
  apply (norm_inverse_solution_sub_le (coerciveFiniteSection P A)
    (coerciveFiniteSection P B) hB u (P g)).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact add_le_add hb (mul_le_mul_of_nonneg_right
    (norm_coerciveFiniteSection_sub_le N A B) (norm_nonneg _))

end lp
