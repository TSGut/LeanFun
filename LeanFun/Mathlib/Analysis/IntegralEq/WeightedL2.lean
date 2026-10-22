/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.Schur
import Mathlib.Tactic.FieldSimp

/-! # Isometric change of density for the weighted Schur test

Division by a positive measurable weight embeds L²(μ) isometrically into
L²(h² μ). The measure h² μ need not be finite. Reference: the classical
weighted Schur test, by conjugation with multiplication by a weight.
-/

@[expose] public noncomputable section
open Filter
open scoped ENNReal InnerProductSpace
namespace MeasureTheory
variable {X : Type*} [MeasurableSpace X]


/-- A measurable real weight with positivity bundled almost everywhere. -/
abbrev PositiveWeight (μ : Measure X) :=
  {h : X → ℝ // Measurable h ∧ ∀ᵐ x ∂μ, 0 < h x}

/-- Existence of the classical density-change isometry, characterized without division. -/
theorem exists_divWeightL2 (μ : Measure X) (w : PositiveWeight μ) :
    ∃ D : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2))),
      ∀ u, ∀ᵐ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2)), D u x*w.val x = u x := by
  classical
  have hh := w.property.1
  let safeWeight (x : X) : Set.Ioi (0 : ℝ) :=
    if h : 0 < w.val x then ⟨w.val x,h⟩ else ⟨1,by norm_num⟩
  have hv (x : X) : (safeWeight x).val = if 0 < w.val x then w.val x else 1 := by
    by_cases h : 0 < w.val x <;> simp only [safeWeight,h,dite_true,dite_false,ite_true,ite_false]
  have hmeas : Measurable (fun x ↦ (safeWeight x).val) := by
    simp_rw [hv]
    exact Measurable.ite (measurableSet_lt measurable_const hh) hh measurable_const
  have hsafe : (fun x ↦ (safeWeight x).val) =ᵐ[μ] w.val := by
    filter_upwards [w.property.2] with x hx
    simp only [hv,ite_eq_left hx]
  have hm (u : Lp ℝ 2 μ) :
      MemLp (fun x ↦ u x/(safeWeight x).val) 2
        (μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2))) := by
    have hsm := (Lp.aestronglyMeasurable u).div₀ hmeas.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq
      (hsm.mono_ac (withDensity_absolutelyContinuous _ _))).mpr
    rw [integrable_withDensity_iff (by fun_prop) (by simp)]
    apply (Lp.memLp u).integrable_sq.congr
    filter_upwards [hsafe] with x hx
    simp only [ENNReal.toReal_ofReal (sq_nonneg (w.val x)),Pi.div_apply]
    rw [← hx]
    field_simp [(show 0 < (safeWeight x).val from (safeWeight x).property).ne']
  let D : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2))) := {
    toFun u := (hm u).toLp _
    map_add' u v := by
      apply Lp.ext
      filter_upwards [(hm (u+v)).coeFn_toLp,
        (hm u).coeFn_toLp,
        (hm v).coeFn_toLp,
        Lp.coeFn_add ((hm u).toLp _) ((hm v).toLp _),
        (withDensity_absolutelyContinuous _ _).ae_le (Lp.coeFn_add u v)] with x hx hu hv hs huv
      simp only [hx, hs, Pi.add_apply, hu, hv, huv, add_div]
    map_smul' r u := by
      change (hm (r • u)).toLp _ = r • _
      apply Lp.ext
      filter_upwards [(hm (r • u)).coeFn_toLp,
        (hm u).coeFn_toLp,
        Lp.coeFn_smul r ((hm u).toLp _),
        (withDensity_absolutelyContinuous _ _).ae_le (Lp.coeFn_smul r u)] with x hx hu hs hru
      simp only [hx, hs, Pi.smul_apply, hu, hru, smul_eq_mul]
      ring
    norm_map' u := by
      change ‖(hm u).toLp _‖ = ‖u‖
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
      rw [integral_congr_ae (show
        (fun x ↦ inner ℝ ((hm u).toLp _ x)
          ((hm u).toLp _ x)) =ᵐ[_]
        (fun x ↦ (u x / (safeWeight x).val)^2) from by
          filter_upwards [(hm u).coeFn_toLp] with x hx
          simp only [hx, Real.inner_apply, pow_two])]
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
      apply integral_congr_ae
      filter_upwards [hsafe] with x hx
      simp only [ENNReal.toReal_ofReal (sq_nonneg (w.val x)), smul_eq_mul, Real.inner_apply]
      rw [← hx]
      field_simp [(show 0 < (safeWeight x).val from (safeWeight x).property).ne']
  }
  refine ⟨D, fun u ↦ ?_⟩
  filter_upwards [(hm u).coeFn_toLp,
    (withDensity_absolutelyContinuous _ _).ae_le hsafe] with x hx hs
  change ((hm u).toLp _) x*w.val x = u x
  rw [hx,← hs]
  exact div_mul_cancel₀ (u x) (show 0 < (safeWeight x).val from (safeWeight x).property).ne'

/-- The unique classical isometry supplied by its multiplicative characterisation. -/
def divWeightL2 (μ : Measure X) (w : PositiveWeight μ) :
    Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2))) :=
  (exists_divWeightL2 μ w).choose

theorem divWeightL2_spec (μ : Measure X) (w : PositiveWeight μ) (u : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2)),
      divWeightL2 μ w u x*w.val x = u x :=
  (exists_divWeightL2 μ w).choose_spec u


/-- The weighted Schur operator, obtained by conjugating the ordinary Schur construction. -/
def weightedSchurL2Operator (μ : Measure X) (κ : Measure (X × X))
    (w : PositiveWeight μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2)))
    (hsnd : κ.map Prod.snd ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2))) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  let D := (divWeightL2 μ w).toContinuousLinearMap
  D.adjoint.comp ((schurL2Operator _ _ κ hC hC hfst hsnd).comp D)

/-- The weighted Schur construction retains the marginal norm bound. -/
theorem norm_weightedSchurL2Operator_le (μ : Measure X) (κ : Measure (X × X))
    (w : PositiveWeight μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2)))
    (hsnd : κ.map Prod.snd ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2))) :
    ‖weightedSchurL2Operator μ κ w hC hfst hsnd‖ ≤ C.toReal := by
  let D := (divWeightL2 μ w).toContinuousLinearMap
  let S := schurL2Operator _ _ κ hC hC hfst hsnd
  have hd : ‖D‖ ≤ 1 := (divWeightL2 μ w).norm_toContinuousLinearMap_le
  have hs : ‖S‖ ≤ C.toReal := by
    simpa [S, Real.mul_self_sqrt ENNReal.toReal_nonneg] using
      norm_schurL2Operator_le _ _ κ hC hC hfst hsnd
  change ‖D.adjoint.comp (S.comp D)‖ ≤ _
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [ContinuousLinearMap.adjoint.norm_map]
  calc
    _ ≤ 1 * (‖S‖ * ‖D‖) := mul_le_mul hd (ContinuousLinearMap.opNorm_comp_le _ _)
      (norm_nonneg _) (by norm_num)
    _ ≤ 1 * (C.toReal * 1) := by gcongr
    _ = _ := by ring



end MeasureTheory
namespace MeasureTheory
open Filter
open scoped ENNReal InnerProductSpace
variable {X : Type*} [MeasurableSpace X]

theorem divWeightL2_unique (μ : Measure X) (w : PositiveWeight μ)
    (D : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2))))
    (hD : ∀ u, ∀ᵐ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2)),
      D u x*w.val x = u x) : D = divWeightL2 μ w := by
  apply LinearIsometry.ext
  intro u
  apply Lp.ext
  filter_upwards [hD u,divWeightL2_spec μ w u,
    (withDensity_absolutelyContinuous _ _).ae_le w.property.2] with x hD hE hpos
  exact mul_right_cancel₀ hpos.ne' (hD.trans hE.symm)

theorem inner_weightedSchurL2Operator (μ : Measure X) (κ : Measure (X × X))
    (w : PositiveWeight μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2)))
    (hsnd : κ.map Prod.snd ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2)))
    (u v : Lp ℝ 2 μ) :
    ⟪v,weightedSchurL2Operator μ κ w hC hfst hsnd u⟫_ℝ =
      ∫ z, divWeightL2 μ w v z.1*divWeightL2 μ w u z.2 ∂κ := by
  rw [weightedSchurL2Operator,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.comp_apply,
    inner_schurL2Operator]
  rfl

theorem integrable_weightedSchurL2_pair (μ : Measure X) (κ : Measure (X × X))
    (w : PositiveWeight μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2)))
    (hsnd : κ.map Prod.snd ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (w.val x^2)))
    (u v : Lp ℝ 2 μ) :
    Integrable (fun z ↦ divWeightL2 μ w v z.1*divWeightL2 μ w u z.2) κ :=
  integrable_schurL2_pair _ _ κ hC hC hfst hsnd
    (divWeightL2 μ w u) (divWeightL2 μ w v)
end MeasureTheory
namespace MeasureTheory
variable {X : Type*} [MeasurableSpace X]
theorem PositiveWeight.spec (μ : Measure X) (w : PositiveWeight μ) :
    Measurable w.val ∧ ∀ᵐ x ∂μ, 0 < w.val x := w.property
end MeasureTheory
