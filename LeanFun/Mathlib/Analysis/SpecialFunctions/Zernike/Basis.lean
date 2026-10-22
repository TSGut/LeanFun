/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Index
public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskIndex
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Complete Zernike bases in finite total-degree spaces
Orthogonality and the dimension count prove completeness. Reference: DLMF 18.37.1–2.
-/

@[expose] public section
open MeasureTheory Module
namespace MvPolynomial

/-- The Zernike family in a finite total-degree space. -/
noncomputable def zernikeDegreeFamily (a b : ℝ) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    restrictTotalDegree (Fin 2) ℝ N :=
  ⟨zernike a b (d.1 0+d.1 1) (d.1 1),
    (mem_restrictTotalDegree (Fin 2) N _).mpr
      ((totalDegree_zernike_le_of_index a b (by omega)).trans
        (by simpa only [sum_exponents_fin_two] using d.2))⟩

/-- All valid triangular Zernike polynomials are linearly independent. -/
theorem zernike_linearIndependent {a b : ℝ}
    (ha : -1 < a) (hb : -1 < b) :
    LinearIndependent ℝ (fun i : Σ n : ℕ, Fin (n+1) ↦ zernike a b i.1 i.2) := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := integralBilinForm (zernikeMeasure a b)
      (hasFiniteMoments_zernikeMeasure ha hb))
  · intro i j hij
    apply integralInner_zernike_eq_zero ha hb (by omega) (by omega)
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
    change integralInner (zernikeMeasure a b) (IntegrablePair.of (zernikeMeasure a b) _ _) ≠ 0
    rw [integralInner_self]
    exact (integral_sq_zernike_pos ha hb (by omega)).ne'

/-- Zernike polynomials form a basis of every complete finite total-degree space. -/
noncomputable def zernikeDegreeBasis {a b : ℝ}
    (ha : -1 < a) (hb : -1 < b) (N : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := by
  classical
  let bmonomial : Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := basisRestrictSupport ℝ _
  have := Module.Finite.finite_basis bmonomial
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  have h := ((zernike_linearIndependent ha hb).comp _ diskIndex_injective).comp
    (fun d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ↦ d.1) Subtype.val_injective
  exact basisOfLinearIndependentOfCardEqFinrank' (zernikeDegreeFamily a b N)
    (LinearIndependent.of_comp (restrictTotalDegree (Fin 2) ℝ N).subtype h)
    (Module.finrank_eq_card_basis bmonomial).symm

/-- The finite basis uses the raw real normalization and the Julia degree ordering. -/
@[simp] theorem zernikeDegreeBasis_apply {a b : ℝ}
    (ha : -1 < a) (hb : -1 < b) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (zernikeDegreeBasis ha hb N d : MvPolynomial (Fin 2) ℝ) =
      zernike a b (d.1 0+d.1 1) (d.1 1) := by
  simp [zernikeDegreeBasis, zernikeDegreeFamily]

end MvPolynomial
