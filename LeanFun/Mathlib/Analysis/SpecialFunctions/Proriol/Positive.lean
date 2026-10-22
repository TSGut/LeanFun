/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Coordinates
public import LeanFun.Mathlib.LinearAlgebra.BilinearForm.PositiveBasis

/-! # Positive polynomial pairing on the Proriol triangle
Complete orthogonal bases with positive norms establish the hypotheses of the
general Gram and Cholesky machinery. Reference: DLMF 18.37.8 and Dunkl–Xu, Chapter 3.
-/

public section
open MeasureTheory Module
namespace MvPolynomial

/-- The standard triangle measure gives a strictly positive polynomial pairing. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasPositiveDefiniteIntegral_proriolMeasure {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) :
    HasPositiveDefiniteIntegral (proriolMeasure α β γ) := by
  classical
  apply HasPositiveDefiniteIntegral.of_positive
  intro p hp
  let N := p.totalDegree
  let V := restrictTotalDegree (Fin 2) ℝ N
  let b := proriolDegreeBasis hα hβ hγ N
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  let B := (integralBilinForm (proriolMeasure α β γ)
    (hasFiniteMoments_proriolMeasure hα hβ hγ)).restrict V
  have ho : ∀ i j, i ≠ j → B (b i) (b j) = 0 :=
    proriolDegreeBasis_orthogonal hα hβ hγ N
  have hn : ∀ i, 0 < B (b i) (b i) := by
    intro i
    change 0 < integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) (b i) (b i))
    simp only [integralInner, b, proriolDegreeBasis_apply, ← pow_two]
    exact integral_sq_proriolMeasure_pos hα hβ hγ _ _
  have hm : p ∈ V := (mem_restrictTotalDegree (Fin 2) N p).mpr le_rfl
  have hp' : (⟨p, hm⟩ : V) ≠ 0 := fun h ↦ hp (congrArg Subtype.val h)
  have he := B.apply_self_pos_of_orthogonal_basis b ho hn hp'
  change 0 < integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) p p) at he
  rwa [integralInner_self] at he

end MvPolynomial
