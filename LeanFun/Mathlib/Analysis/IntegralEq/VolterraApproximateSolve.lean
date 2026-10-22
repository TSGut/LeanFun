/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraSolve
public import LeanFun.Mathlib.Analysis.Normed.Operator.ApproximateFiniteSection
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Volterra solves with approximated kernels

The kernel and section size may be refined simultaneously. Uniform kernel
errors control coefficient operator errors, eventual stability and solution
convergence. Reference: Gutleb–Olver, arXiv:1906.03907, §3.
-/

@[expose] public noncomputable section
open Polynomial Set Filter ContinuousLinearMap
open scoped Topology
namespace Real
variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
  {M : ℝ} (hM : 0 ≤ M) (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M)

/-- Uniform kernel errors retain their bound in normalized coefficient coordinates. -/
theorem norm_volterraL2CoefficientOperator_sub_le
    {L : (Fin 2 → ℝ) → ℝ} (hL : ContinuousOn L volterraTriangle)
    {B δ : ℝ} (hB : 0 ≤ B) (bL : ∀ z ∈ volterraTriangle, |L z| ≤ B)
    (hδ : 0 ≤ δ) (err : ∀ z ∈ volterraTriangle, |K z - L z| ≤ δ) :
    ‖volterraL2CoefficientOperator hK hM bK - volterraL2CoefficientOperator hL hB bL‖ ≤ δ := by
  rw [volterraL2CoefficientOperator, volterraL2CoefficientOperator,
    HilbertBasis.norm_coefficientOperator_sub]
  exact norm_volterraL2Operator_sub_le hK hL hM hB bK bL hδ err

variable {Ks : ℕ → (Fin 2 → ℝ) → ℝ}
  (hs : ∀ n, ContinuousOn (Ks n) volterraTriangle)
  {B e : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n)
  (bs : ∀ n z, z ∈ volterraTriangle → |Ks n z| ≤ B n)
  (he : ∀ n, 0 ≤ e n)
  (err : ∀ n z, z ∈ volterraTriangle → |Ks n z - K z| ≤ e n)
  (hte : Tendsto e atTop (𝓝 0))

/-- The section family for simultaneously varying kernels and cutoffs. -/
def approximateVolterraCoefficientSection (N : ℕ) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  volterraCoefficientSection (hs N) (hB N) (bs N) N

/-- Each approximate section keeps the identity on unresolved output coordinates. -/
theorem approximateVolterraCoefficientSection_apply (N : ℕ) (u : lp (fun _ : ℕ ↦ ℝ) 2) :
    approximateVolterraCoefficientSection hs hB bs N u =
      u - lp.initialL2Projection N (volterraL2CoefficientOperator (hs N) (hB N) (bs N) u) := by
  simp only [approximateVolterraCoefficientSection, volterraCoefficientSection,
    liftedFiniteSection, add_apply, one_apply_eq_self, comp_apply, _root_.neg_apply, map_neg,
    sub_eq_add_neg]

include hK hM bK he err hte

/-- Vanishing kernel errors give norm convergence of normalized coefficient operators. -/
theorem tendsto_volterraL2CoefficientOperator_of_error_bounds :
    Tendsto (fun n ↦ volterraL2CoefficientOperator (hs n) (hB n) (bs n)) atTop
      (𝓝 (volterraL2CoefficientOperator hK hM bK)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_volterraL2CoefficientOperator_sub_le (hs n) (hB n) (bs n)
      hK hM bK (he n) (err n)) hte

/-- Approximating the kernel while increasing section size preserves eventual stability. -/
private theorem eventually_stable_approximateVolterraSection_ringInverse :
    ∀ᶠ n in atTop, IsUnit (volterraCoefficientSection (hs n) (hB n) (bs n) n) ∧
      ‖Ring.inverse (volterraCoefficientSection (hs n) (hB n) (bs n) n)‖ ≤
        ‖Ring.inverse (1 - volterraL2CoefficientOperator hK hM bK)‖ + 1 := by
  have ht := tendsto_volterraL2CoefficientOperator_of_error_bounds hK hM bK hs hB bs he err hte
  simpa only [volterraCoefficientSection, sub_eq_add_neg] using
    eventually_stable_approximateLiftedFiniteSection_ringInverse _ lp.norm_initialL2Projection_le
      lp.tendsto_initialL2Projection (-volterraL2CoefficientOperator hK hM bK)
      (isCompactOperator_volterraL2CoefficientOperator hK hM bK).neg
      (by simpa only [sub_eq_add_neg] using isUnit_one_sub_volterraL2CoefficientOperator hK hM bK)
      _ ht.neg

/-- Each sufficiently large approximating finite system has a unique solution. -/
theorem eventually_existsUnique_approximateVolterra_solution :
    ∀ᶠ n in atTop, ∀ f : lp (fun _ : ℕ ↦ ℝ) 2,
      ∃! u, lp.initialL2Projection n u = u ∧
        lp.initialL2Projection n (u - volterraL2CoefficientOperator (hs n) (hB n) (bs n) u) =
          lp.initialL2Projection n f := by
  filter_upwards [eventually_stable_approximateVolterraSection_ringInverse hK hM bK hs hB bs he err hte] with n hn f
  simpa only [add_apply, one_apply_eq_self, _root_.neg_apply, sub_eq_add_neg] using
    existsUnique_projected_solution (lp.initialL2Projection n)
      (-volterraL2CoefficientOperator (hs n) (hB n) (bs n))
      (lp.initialL2Projection_idempotent n)
      (show IsUnit (liftedFiniteSection (lp.initialL2Projection n)
        (-volterraL2CoefficientOperator (hs n) (hB n) (bs n))) from hn.1) f

/-- The solve error splits into the exact solution's projection tail and the
uniform kernel error times the solution norm. -/
private theorem eventually_norm_approximateVolterra_error_le_ringInverse :
    ∀ᶠ n in atTop, ∀ u : lp (fun _ : ℕ ↦ ℝ) 2,
      ‖Ring.inverse (volterraCoefficientSection (hs n) (hB n) (bs n) n)
        (lp.initialL2Projection n (u - volterraL2CoefficientOperator hK hM bK u)) - u‖ ≤
        (‖Ring.inverse (1 - volterraL2CoefficientOperator hK hM bK)‖ + 1) *
          (‖lp.initialL2Projection n u - u‖ + e n * ‖u‖) := by
  filter_upwards [eventually_stable_approximateVolterraSection_ringInverse hK hM bK hs hB bs he err hte] with n hn u
  have h := norm_approximateLiftedFiniteSection_error_le_ringInverse (lp.initialL2Projection n)
    (-volterraL2CoefficientOperator hK hM bK)
    (-volterraL2CoefficientOperator (hs n) (hB n) (bs n))
    (lp.norm_initialL2Projection_le n) hn.1 u
  simp only [← sub_eq_add_neg, neg_sub_neg] at h
  refine h.trans (mul_le_mul hn.2 ?_ (by positivity) (by positivity))
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (norm_volterraL2CoefficientOperator_sub_le (hs n) (hB n) (bs n)
      hK hM bK (he n) (err n)) (norm_nonneg u))

/-- Simultaneous kernel approximation and finite solves converge for every L² RHS. -/
private theorem tendsto_approximateVolterra_solution_ringInverse (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun n ↦ Ring.inverse (volterraCoefficientSection (hs n) (hB n) (bs n) n)
      (lp.initialL2Projection n f)) atTop
      (𝓝 (Ring.inverse (1 - volterraL2CoefficientOperator hK hM bK) f)) := by
  have ht := tendsto_approximateLiftedFiniteSection _ lp.norm_initialL2Projection_le
    lp.tendsto_initialL2Projection (-volterraL2CoefficientOperator hK hM bK)
    (isCompactOperator_volterraL2CoefficientOperator hK hM bK).neg _
    (tendsto_volterraL2CoefficientOperator_of_error_bounds hK hM bK hs hB bs he err hte).neg
  have hi := tendsto_inverse_of_tendsto ht
    (by simpa only [sub_eq_add_neg] using isUnit_one_sub_volterraL2CoefficientOperator hK hM bK)
  simpa only [volterraCoefficientSection, sub_eq_add_neg, Function.comp_def] using
    ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.tendsto _).comp
      (hi.prodMk_nhds (lp.tendsto_initialL2Projection f))


/-- Approximate section stability includes the existence of each inverse value. -/
theorem eventually_stable_approximateVolterraSection :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (approximateVolterraCoefficientSection hs hB bs n),
      ‖Ring.inverseAt (approximateVolterraCoefficientSection hs hB bs) ⟨n, hn⟩‖ ≤
        ‖volterraCoefficientInverse hK hM bK‖ + 1 := by
  filter_upwards [eventually_stable_approximateVolterraSection_ringInverse hK hM bK hs hB bs he err hte]
    with n hn
  have hu : IsUnit (approximateVolterraCoefficientSection hs hB bs n) := hn.1
  refine ⟨hu, ?_⟩
  rw [Ring.inverseAt_eq_ringInverse]
  simpa only [approximateVolterraCoefficientSection, volterraCoefficientInverse_eq_ringInverse] using hn.2

/-- The approximate-section limiting filter is nontrivial. -/
theorem approximateVolterraSection_filter_neBot :
    NeBot (Ring.invertibleIndexFilter (approximateVolterraCoefficientSection hs hB bs) atTop) :=
  Ring.invertibleIndexFilter_neBot _ _
    ((eventually_stable_approximateVolterraSection_ringInverse hK hM bK hs hB bs he err hte).mono
      (fun _ h ↦ h.1))

/-- Projection and kernel errors control every sufficiently large classical section solve. -/
theorem eventually_norm_approximateVolterra_error_le :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (approximateVolterraCoefficientSection hs hB bs n),
      ∀ u : lp (fun _ : ℕ ↦ ℝ) 2,
      ‖Ring.inverseAt (approximateVolterraCoefficientSection hs hB bs) ⟨n, hn⟩
        (lp.initialL2Projection n (u - volterraL2CoefficientOperator hK hM bK u)) - u‖ ≤
        (‖volterraCoefficientInverse hK hM bK‖ + 1) *
          (‖lp.initialL2Projection n u - u‖ + e n * ‖u‖) := by
  filter_upwards [eventually_stable_approximateVolterraSection_ringInverse hK hM bK hs hB bs he err hte,
    eventually_norm_approximateVolterra_error_le_ringInverse hK hM bK hs hB bs he err hte]
      with n hn heN
  have hu : IsUnit (approximateVolterraCoefficientSection hs hB bs n) := hn.1
  refine ⟨hu, fun u ↦ ?_⟩
  rw [Ring.inverseAt_eq_ringInverse]
  simpa only [approximateVolterraCoefficientSection, volterraCoefficientInverse_eq_ringInverse] using heN u

/-- Simultaneous kernel approximation and finite solves converge on their actual domain. -/
theorem tendsto_approximateVolterra_solution (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun n : Ring.InvertibleIndex (approximateVolterraCoefficientSection hs hB bs) ↦
      Ring.inverseAt (approximateVolterraCoefficientSection hs hB bs) n (lp.initialL2Projection n f))
      (Ring.invertibleIndexFilter (approximateVolterraCoefficientSection hs hB bs) atTop)
      (𝓝 (volterraCoefficientInverse hK hM bK f)) := by
  have h := (tendsto_approximateVolterra_solution_ringInverse hK hM bK hs hB bs he err hte f).comp
    (Filter.tendsto_comap : Tendsto
      (Subtype.val : Ring.InvertibleIndex (approximateVolterraCoefficientSection hs hB bs) → ℕ)
      (Filter.comap Subtype.val atTop) atTop)
  rw [volterraCoefficientInverse_eq_ringInverse]
  apply h.congr'
  exact Filter.Eventually.of_forall (fun n ↦ by
    dsimp only [Function.comp_def]
    rw [Ring.inverseAt_eq_ringInverse]
    rfl)

end Real
