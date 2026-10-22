/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.MixedPairing
public import LeanFun.Mathlib.LinearAlgebra.BilinearForm.OrthogonalCoordinates

/-! # Proriol coordinates and sparse outer-parameter conversion
These are actual finite-basis coordinates in the DLMF normalization; squared
norms appear in the denominator. Reference: DLMF 18.37 and orthogonal projection.
-/

public section
open MeasureTheory Module
namespace MvPolynomial

/-- Distinct finite basis members are orthogonal in the standard triangle measure. -/
theorem proriolDegreeBasis_orthogonal {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) (hij : i ≠ j) :
    integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) (proriolDegreeBasis hα hβ hγ N i) (proriolDegreeBasis hα hβ hγ N j)) = 0 := by
  simp only [proriolDegreeBasis_apply]
  apply integralInner_proriolMeasure_eq_zero hα hβ hγ (by omega) (by omega)
  intro h
  apply hij
  apply Subtype.ext
  have hn := congrArg Prod.fst h
  have hk := congrArg Prod.snd h
  ext t
  fin_cases t <;> dsimp at hn hk ⊢ <;> omega

/-- Coordinates in the unnormalized Proriol basis are integral projections divided by norms. -/
theorem proriolDegreeBasis_repr {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ)
    (p : restrictTotalDegree (Fin 2) ℝ N)
    (i : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (proriolDegreeBasis hα hβ hγ N).repr p i =
      integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) p (proriol α β γ (i.1 0+i.1 1) (i.1 1))) /
      (∫ v, (eval v (proriol α β γ (i.1 0+i.1 1) (i.1 1)))^2
        ∂proriolMeasure α β γ) := by
  classical
  let b := proriolDegreeBasis hα hβ hγ N
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  let B := (integralBilinForm (proriolMeasure α β γ)
    (hasFiniteMoments_proriolMeasure hα hβ hγ)).restrict (restrictTotalDegree (Fin 2) ℝ N)
  have ho : ∀ i j, i ≠ j → B (b i) (b j) = 0 :=
    proriolDegreeBasis_orthogonal hα hβ hγ N
  have hn : ∀ i, B (b i) (b i) ≠ 0 := by
    intro i
    change integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) (b i) (b i)) ≠ 0
    simp only [integralInner, b, proriolDegreeBasis_apply, ← pow_two]
    exact (integral_sq_proriolMeasure_pos hα hβ hγ _ _).ne'
  have he := B.basis_repr_eq_div b ho hn p i
  change b.repr p i = integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) p (b i)) /
    integralInner (proriolMeasure α β γ) (IntegrablePair.of (proriolMeasure α β γ) (b i) (b i)) at he
  dsimp only [integralInner, IntegrablePair.of] at he ⊢
  simpa only [b, proriolDegreeBasis_apply, ← pow_two] using he

/-- Actual alpha-raising connection coefficients have bandwidth r and preserve inner degree. -/
theorem proriol_alpha_connection_eq_zero {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (r N : ℕ)
    (hαr : -1 < α+r)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N})
    (hgap : i.1 1 ≠ j.1 1 ∨ i.1 0+i.1 1 < j.1 0+j.1 1 ∨
      j.1 0+j.1 1+r < i.1 0+i.1 1) :
    (proriolDegreeBasis hαr hβ hγ N).repr (proriolDegreeBasis hα hβ hγ N i) j = 0 := by
  rw [proriolDegreeBasis_repr]
  simp only [proriolDegreeBasis_apply]
  rw [integralInner_proriol_alpha_shift_eq_zero hα hβ hγ r (by omega) (by omega) hgap,
    zero_div]

end MvPolynomial
