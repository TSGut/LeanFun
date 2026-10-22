/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.WeightedL2

/-! # Weighted Schur operators between two measure spaces

Independent positive auxiliary weights on the input and output spaces give
norm bound sqrt(C D). Reference: the classical two-weight Schur test.
-/

@[expose] public noncomputable section
open scoped ENNReal InnerProductSpace
namespace MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The weighted Schur operator, obtained by conjugating the ordinary Schur construction. -/
def twoWeightSchurL2Operator (μ : Measure X) (ν : Measure Y) (κ : Measure (X × Y))
    (h : PositiveWeight μ) (g : PositiveWeight ν)
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (h.val x^2)))
    (hsnd : κ.map Prod.snd ≤ D • ν.withDensity (fun y ↦ ENNReal.ofReal (g.val y^2))) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (divWeightL2 μ h).toContinuousLinearMap.adjoint.comp
    ((schurL2Operator _ _ κ hC hD hfst hsnd).comp
      (divWeightL2 ν g).toContinuousLinearMap)

/-- The weighted Schur construction retains the marginal norm bound. -/
theorem norm_twoWeightSchurL2Operator_le (μ : Measure X) (ν : Measure Y) (κ : Measure (X × Y))
    (h : PositiveWeight μ) (g : PositiveWeight ν)
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (h.val x^2)))
    (hsnd : κ.map Prod.snd ≤ D • ν.withDensity (fun y ↦ ENNReal.ofReal (g.val y^2))) :
    ‖twoWeightSchurL2Operator μ ν κ h g hC hD hfst hsnd‖ ≤
      Real.sqrt C.toReal * Real.sqrt D.toReal := by
  let A := (divWeightL2 μ h).toContinuousLinearMap
  let B := (divWeightL2 ν g).toContinuousLinearMap
  let S := schurL2Operator _ _ κ hC hD hfst hsnd
  have ha : ‖A‖ ≤ 1 := (divWeightL2 μ h).norm_toContinuousLinearMap_le
  have hb : ‖B‖ ≤ 1 := (divWeightL2 ν g).norm_toContinuousLinearMap_le
  have hs := norm_schurL2Operator_le _ _ κ hC hD hfst hsnd
  change ‖A.adjoint.comp (S.comp B)‖ ≤ _
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [ContinuousLinearMap.adjoint.norm_map]
  calc
    _ ≤ 1 * (‖S‖ * ‖B‖) := mul_le_mul ha (ContinuousLinearMap.opNorm_comp_le _ _)
      (norm_nonneg _) (by norm_num)
    _ ≤ 1 * ((Real.sqrt C.toReal * Real.sqrt D.toReal) * 1) := by gcongr
    _ = _ := by ring

/-- The pairing uses the genuine density-change L² vectors. -/
theorem inner_twoWeightSchurL2Operator (μ : Measure X) (ν : Measure Y) (κ : Measure (X × Y))
    (h : PositiveWeight μ) (g : PositiveWeight ν)
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (h.val x^2)))
    (hsnd : κ.map Prod.snd ≤ D • ν.withDensity (fun y ↦ ENNReal.ofReal (g.val y^2)))
    (u : Lp ℝ 2 ν) (v : Lp ℝ 2 μ) :
    ⟪v,twoWeightSchurL2Operator μ ν κ h g hC hD hfst hsnd u⟫_ℝ =
      ∫ z, divWeightL2 μ h v z.1*divWeightL2 ν g u z.2 ∂κ := by
  rw [twoWeightSchurL2Operator,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.comp_apply,
    inner_schurL2Operator]
  rfl

/-- The classical pairing is integrable for all L² inputs. -/
theorem integrable_twoWeightSchurL2_pair (μ : Measure X) (ν : Measure Y) (κ : Measure (X × Y))
    (h : PositiveWeight μ) (g : PositiveWeight ν)
    {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞)
    (hfst : κ.map Prod.fst ≤ C • μ.withDensity (fun x ↦ ENNReal.ofReal (h.val x^2)))
    (hsnd : κ.map Prod.snd ≤ D • ν.withDensity (fun y ↦ ENNReal.ofReal (g.val y^2)))
    (u : Lp ℝ 2 ν) (v : Lp ℝ 2 μ) :
    Integrable (fun z ↦ divWeightL2 μ h v z.1*divWeightL2 ν g u z.2) κ :=
  integrable_schurL2_pair _ _ κ hC hD hfst hsnd (divWeightL2 ν g u) (divWeightL2 μ h v)
end MeasureTheory
