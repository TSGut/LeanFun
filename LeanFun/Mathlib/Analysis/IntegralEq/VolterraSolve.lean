/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraCompact
public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraIterates
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Stable finite-section Volterra solves

The continuous-kernel second-kind equation is invertible without a smallness
hypothesis. Compactness gives eventual finite-section invertibility, a uniform
inverse bound and convergence to the L² solution. The lifted map is I-P_N A;
on the projection range this is exactly the finite matrix I-P_N A P_N.
Reference: Gutleb–Olver, arXiv:1906.03907, and compact finite-section stability.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter ContinuousLinearMap
open scoped Topology
namespace Real
variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
  {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |K z| ≤ M)

/-- Normalized coefficient coordinates preserve second-kind invertibility. -/
theorem isUnit_one_sub_volterraL2CoefficientOperator :
    IsUnit (1 - volterraL2CoefficientOperator hK hM hb) := by
  let b := hilbertBasisShiftedJacobi (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0)
  have h := (isUnit_one_sub_volterraL2Operator hK hM hb).map
    b.repr.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toMonoidHom
  change IsUnit (b.repr.toContinuousLinearEquiv.conjContinuousAlgEquiv
    (1 - volterraL2Operator hK hM hb)) at h
  rw [map_sub, map_one] at h
  exact h

/-- The classical inverse of the second-kind normalized coefficient operator. -/
def volterraCoefficientInverse :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  ↑((isUnit_one_sub_volterraL2CoefficientOperator hK hM hb).unit⁻¹)

/-- The inverse has the two defining operator identities. -/
theorem volterraCoefficientInverse_mul :
    volterraCoefficientInverse hK hM hb * (1 - volterraL2CoefficientOperator hK hM hb) = 1 ∧
      (1 - volterraL2CoefficientOperator hK hM hb) * volterraCoefficientInverse hK hM hb = 1 := by
  exact ⟨by simpa only [volterraCoefficientInverse, IsUnit.unit_spec] using
      Units.inv_mul (isUnit_one_sub_volterraL2CoefficientOperator hK hM hb).unit,
    by simpa only [volterraCoefficientInverse, IsUnit.unit_spec] using
      Units.mul_inv (isUnit_one_sub_volterraL2CoefficientOperator hK hM hb).unit⟩

/-- Internal imported-inverse bridge, whose operator is always invertible. -/
theorem volterraCoefficientInverse_eq_ringInverse :
    volterraCoefficientInverse hK hM hb =
      Ring.inverse (1 - volterraL2CoefficientOperator hK hM hb) := by
  simpa only [volterraCoefficientInverse, IsUnit.unit_spec] using
    (Ring.inverse_unit (isUnit_one_sub_volterraL2CoefficientOperator hK hM hb).unit).symm

/-- Lifted normalized finite-section equations retain the identity on unresolved rows. -/
def volterraCoefficientSection (N : ℕ) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  liftedFiniteSection (lp.initialL2Projection N) (-volterraL2CoefficientOperator hK hM hb)

/-- The lifted section keeps the identity on unresolved output coordinates. -/
theorem volterraCoefficientSection_apply (N : ℕ) (u : lp (fun _ : ℕ ↦ ℝ) 2) :
    volterraCoefficientSection hK hM hb N u =
      u - lp.initialL2Projection N (volterraL2CoefficientOperator hK hM hb u) := by
  simp only [volterraCoefficientSection, liftedFiniteSection, add_apply, one_apply_eq_self,
    comp_apply, _root_.neg_apply, map_neg, sub_eq_add_neg]

/-- All sufficiently large normalized sections are invertible with a uniform inverse bound. -/
private theorem eventually_stable_volterraCoefficientSection_ringInverse :
    ∀ᶠ N in atTop, IsUnit (volterraCoefficientSection hK hM hb N) ∧
      ‖Ring.inverse (volterraCoefficientSection hK hM hb N)‖ ≤
        ‖Ring.inverse (1 - volterraL2CoefficientOperator hK hM hb)‖ + 1 := by
  simpa only [sub_eq_add_neg, volterraCoefficientSection] using
    eventually_stable_liftedFiniteSection_ringInverse _ lp.norm_initialL2Projection_le
      lp.tendsto_initialL2Projection (-volterraL2CoefficientOperator hK hM hb)
      (isCompactOperator_volterraL2CoefficientOperator hK hM hb).neg
      (by simpa only [sub_eq_add_neg] using isUnit_one_sub_volterraL2CoefficientOperator hK hM hb)

/-- Sufficiently large finite matrices have a unique solution within their coordinate range. -/
theorem eventually_existsUnique_volterra_projected_solution :
    ∀ᶠ N in atTop, ∀ f : lp (fun _ : ℕ ↦ ℝ) 2,
      ∃! u, lp.initialL2Projection N u = u ∧
        lp.initialL2Projection N (u - volterraL2CoefficientOperator hK hM hb u) =
          lp.initialL2Projection N f := by
  filter_upwards [eventually_stable_volterraCoefficientSection_ringInverse hK hM hb] with N hN f
  simpa only [add_apply, one_apply_eq_self, _root_.neg_apply, sub_eq_add_neg] using
    existsUnique_projected_solution (lp.initialL2Projection N)
      (-volterraL2CoefficientOperator hK hM hb)
      (lp.initialL2Projection_idempotent N)
      (show IsUnit (liftedFiniteSection (lp.initialL2Projection N)
        (-volterraL2CoefficientOperator hK hM hb)) from hN.1) f

/-- The normalized finite-section error is bounded by a fixed multiple of the exact solution tail. -/
private theorem eventually_norm_volterraCoefficientSection_error_le_ringInverse :
    ∀ᶠ N in atTop, ∀ u : lp (fun _ : ℕ ↦ ℝ) 2,
      ‖Ring.inverse (volterraCoefficientSection hK hM hb N)
        (lp.initialL2Projection N (u - volterraL2CoefficientOperator hK hM hb u)) - u‖ ≤
        (‖Ring.inverse (1 - volterraL2CoefficientOperator hK hM hb)‖ + 1) *
          ‖lp.initialL2Projection N u - u‖ := by
  simpa only [volterraCoefficientSection, sub_eq_add_neg, add_apply, one_apply_eq_self, _root_.neg_apply] using
    eventually_norm_liftedFiniteSection_error_le_ringInverse _ lp.norm_initialL2Projection_le
      lp.tendsto_initialL2Projection (-volterraL2CoefficientOperator hK hM hb)
      (isCompactOperator_volterraL2CoefficientOperator hK hM hb).neg
      (by simpa only [sub_eq_add_neg] using isUnit_one_sub_volterraL2CoefficientOperator hK hM hb)

/-- Finite-section solutions converge for every L² coefficient right-hand side. -/
private theorem tendsto_volterraCoefficientSection_solution_ringInverse (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N ↦ Ring.inverse (volterraCoefficientSection hK hM hb N)
      (lp.initialL2Projection N f)) atTop
      (𝓝 (Ring.inverse (1 - volterraL2CoefficientOperator hK hM hb) f)) := by
  have ht := tendsto_liftedFiniteSection _ lp.norm_initialL2Projection_le
    lp.tendsto_initialL2Projection (-volterraL2CoefficientOperator hK hM hb)
      (isCompactOperator_volterraL2CoefficientOperator hK hM hb).neg
  have hi : Tendsto (fun n ↦ Ring.inverse (liftedFiniteSection (lp.initialL2Projection n)
      (-volterraL2CoefficientOperator hK hM hb))) atTop
      (𝓝 (Ring.inverse (1 + -volterraL2CoefficientOperator hK hM hb))) :=
    tendsto_inverse_of_tendsto ht
    (by simpa only [sub_eq_add_neg] using isUnit_one_sub_volterraL2CoefficientOperator hK hM hb)
  simpa only [volterraCoefficientSection, sub_eq_add_neg, Function.comp_def] using
    ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.tendsto _).comp
      (hi.prodMk_nhds (lp.tendsto_initialL2Projection f))


/-- Stable second-kind sections provide an inverse certificate and a uniform bound. -/
theorem eventually_stable_volterraCoefficientSection :
    ∀ᶠ N in atTop, ∃ hN : IsUnit (volterraCoefficientSection hK hM hb N),
      ‖Ring.inverseAt (volterraCoefficientSection hK hM hb) ⟨N, hN⟩‖ ≤
        ‖volterraCoefficientInverse hK hM hb‖ + 1 := by
  filter_upwards [eventually_stable_volterraCoefficientSection_ringInverse hK hM hb] with N hN
  refine ⟨hN.1, ?_⟩
  simpa only [Ring.inverseAt_eq_ringInverse, volterraCoefficientInverse_eq_ringInverse] using hN.2

/-- The domain of invertible second-kind sections is cofinal and nontrivial. -/
theorem volterraCoefficientSection_filter_neBot :
    NeBot (Ring.invertibleIndexFilter (volterraCoefficientSection hK hM hb) atTop) :=
  Ring.invertibleIndexFilter_neBot _ _
    ((eventually_stable_volterraCoefficientSection_ringInverse hK hM hb).mono (fun _ h ↦ h.1))

/-- The classical section error is controlled by the exact solution tail. -/
theorem eventually_norm_volterraCoefficientSection_error_le :
    ∀ᶠ N in atTop, ∃ hN : IsUnit (volterraCoefficientSection hK hM hb N),
      ∀ u : lp (fun _ : ℕ ↦ ℝ) 2,
      ‖Ring.inverseAt (volterraCoefficientSection hK hM hb) ⟨N, hN⟩
        (lp.initialL2Projection N (u - volterraL2CoefficientOperator hK hM hb u)) - u‖ ≤
        (‖volterraCoefficientInverse hK hM hb‖ + 1) * ‖lp.initialL2Projection N u - u‖ := by
  filter_upwards [eventually_stable_volterraCoefficientSection_ringInverse hK hM hb,
    eventually_norm_volterraCoefficientSection_error_le_ringInverse hK hM hb] with N hN he
  refine ⟨hN.1, fun u ↦ ?_⟩
  simpa only [Ring.inverseAt_eq_ringInverse, volterraCoefficientInverse_eq_ringInverse] using he u

/-- Second-kind solutions converge through the invertible-cutoff domain. -/
theorem tendsto_volterraCoefficientSection_solution (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N : Ring.InvertibleIndex (volterraCoefficientSection hK hM hb) ↦
      Ring.inverseAt (volterraCoefficientSection hK hM hb) N (lp.initialL2Projection N f))
      (Ring.invertibleIndexFilter (volterraCoefficientSection hK hM hb) atTop)
      (𝓝 (volterraCoefficientInverse hK hM hb f)) := by
  have h := (tendsto_volterraCoefficientSection_solution_ringInverse hK hM hb f).comp
    (Filter.tendsto_comap : Tendsto
      (Subtype.val : Ring.InvertibleIndex (volterraCoefficientSection hK hM hb) → ℕ)
      (Filter.comap Subtype.val atTop) atTop)
  simpa only [Ring.invertibleIndexFilter, Function.comp_def, Ring.inverseAt_eq_ringInverse,
    volterraCoefficientInverse_eq_ringInverse] using h

end Real
