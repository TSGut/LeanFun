/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Orthogonality
public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskIndex
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Complete Proriol bases in finite total-degree spaces
Orthogonality and the dimension count prove completeness. Reference: DLMF 18.37.7–8.
-/

@[expose] public section
open MeasureTheory Module
namespace MvPolynomial

/-- The Proriol family in a finite total-degree space. -/
noncomputable def proriolDegreeFamily (α β γ : ℝ) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    restrictTotalDegree (Fin 2) ℝ N :=
  ⟨proriol α β γ (d.1 0+d.1 1) (d.1 1),
    (mem_restrictTotalDegree (Fin 2) N _).mpr
      ((totalDegree_proriol_le α β γ (by omega)).trans
        (by simpa only [sum_exponents_fin_two] using d.2))⟩

/-- All valid triangular Proriol polynomials are linearly independent. -/
theorem proriol_linearIndependent {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) :
    LinearIndependent ℝ (fun i : Σ n : ℕ, Fin (n+1) ↦ proriol α β γ i.1 i.2) := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := integralBilinForm (proriolProductMeasure α β γ)
      (hasFiniteMoments_proriolProductMeasure hα hβ hγ))
  · intro i j hij
    apply integralInner_proriol_eq_zero hα hβ hγ (by omega) (by omega)
    intro h
    apply hij
    have hn := congrArg Prod.fst h
    have hk := congrArg Prod.snd h
    rcases i with ⟨n,k⟩
    rcases j with ⟨m,l⟩
    dsimp at hn hk
    subst m
    congr 1
    exact Fin.ext hk
  · intro i
    change integralInner (proriolProductMeasure α β γ) (IntegrablePair.of (proriolProductMeasure α β γ) _ _) ≠ 0
    rw [integralInner_self]
    exact (integral_sq_proriol_pos hα hβ hγ _ _).ne'

/-- Proriol polynomials form a basis of every complete finite total-degree space. -/
noncomputable def proriolDegreeBasis {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := by
  classical
  let b : Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := basisRestrictSupport ℝ _
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  have h := ((proriol_linearIndependent hα hβ hγ).comp _ diskIndex_injective).comp
    (fun d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ↦ d.1) Subtype.val_injective
  exact basisOfLinearIndependentOfCardEqFinrank' (proriolDegreeFamily α β γ N)
    (LinearIndependent.of_comp (restrictTotalDegree (Fin 2) ℝ N).subtype h)
    (Module.finrank_eq_card_basis b).symm

/-- The finite basis uses the DLMF normalization, without rescaling its members. -/
@[simp] theorem proriolDegreeBasis_apply {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (proriolDegreeBasis hα hβ hγ N d : MvPolynomial (Fin 2) ℝ) =
      proriol α β γ (d.1 0+d.1 1) (d.1 1) := by
  simp [proriolDegreeBasis, proriolDegreeFamily]

end MvPolynomial
