/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraRawL2Bridge
public import LeanFun.Mathlib.Analysis.IntegralEq.JacobiVolterraInjectivity
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraToeplitzSections
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraApproximation
@[expose] public noncomputable section
/-! # Genuine raw Volterra injectivity and positive-diagonal sections

The weighted function realization discharges the injectivity hypothesis in the
Toeplitz finite-section theorem. Reference: Gutleb's thesis, §2.7, and the
coercive-plus-compact finite-section method of Böttcher--Silbermann.
-/

open Polynomial Set Filter ContinuousLinearMap
open scoped Topology
namespace MvPolynomial
/-- A nonvanishing kernel diagonal gives injectivity on the full raw coefficient space. -/
theorem injective_volterraPreconditionedL2 (K : MvPolynomial (Fin 2) ℝ)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) :
    Function.Injective (volterraPreconditionedL2 K) := by
  obtain ⟨M,hb⟩ := isCompact_volterraTriangle.exists_bound_of_continuousOn K.continuous_eval.continuousOn
  have hb' : ∀ z ∈ Real.volterraTriangle, |eval z K| ≤ |M| :=
    fun z hz ↦ (hb z hz).trans (le_abs_self M)
  have he := jacobiVolterraL2Operator_raw_synthesis K (abs_nonneg M) hb'
  intro u v huv
  apply shiftedJacobiOneZeroSynthesis_injective
  apply injective_jacobiVolterraL2Operator K (abs_nonneg M) hb' hdiag
  have hu := congrArg (fun A ↦ A u) he
  have hv := congrArg (fun A ↦ A v) he
  simp only [ContinuousLinearMap.comp_apply] at hu hv
  rw [← hu, ← hv, huv]
/-- A positive kernel diagonal makes the raw ordered operator invertible. -/
theorem isUnit_volterraPreconditionedL2_of_pos (K : MvPolynomial (Fin 2) ℝ)
    {a : ℝ} (ha : 0 < a) (hK : ∀ x ∈ Icc (0 : ℝ) 1, a ≤ eval (fun _ ↦ x) K) :
    IsUnit (volterraPreconditionedL2 K) :=
  isUnit_volterraPreconditionedL2_of_injective K ha hK
    (injective_volterraPreconditionedL2 K (fun x hx ↦ (ha.trans_le (hK x hx)).ne'))
/-- Positive diagonal alone gives eventual invertibility of leading raw sections. -/
theorem eventually_isUnit_volterraPreconditionedL2_section_of_pos (K : MvPolynomial (Fin 2) ℝ)
    {a : ℝ} (ha : 0 < a) (hK : ∀ x ∈ Icc (0 : ℝ) 1, a ≤ eval (fun _ ↦ x) K) :
    ∀ᶠ N in atTop, IsUnit (coerciveFiniteSection (lp.initialL2Projection N)
      (volterraPreconditionedL2 K)) :=
  eventually_isUnit_volterraPreconditionedL2_section K ha hK
    (injective_volterraPreconditionedL2 K (fun x hx ↦ (ha.trans_le (hK x hx)).ne'))
/-- Raw leading-section solves converge without a separate injectivity assumption. -/
theorem tendsto_volterraPreconditionedL2_section_solution_of_pos (K : MvPolynomial (Fin 2) ℝ)
    {a : ℝ} (ha : 0 < a) (hK : ∀ x ∈ Icc (0 : ℝ) 1, a ≤ eval (fun _ ↦ x) K)
    (g : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun N ↦ Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
      (volterraPreconditionedL2 K)) (lp.initialL2Projection N g)) atTop
      (𝓝 (Ring.inverse (volterraPreconditionedL2 K) g)) :=
  tendsto_volterraPreconditionedL2_section_solution K ha hK
    (injective_volterraPreconditionedL2 K (fun x hx ↦ (ha.trans_le (hK x hx)).ne')) g
end MvPolynomial
