/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusBasic
public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskIndex
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Complete Zernike annular bases in finite total-degree spaces
Orthogonality and the dimension count prove completeness.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public section
open MeasureTheory Module Set
namespace MvPolynomial

/-- The Zernike family in a finite total-degree space. -/
noncomputable def zernikeAnnulusDegreeFamily {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    restrictTotalDegree (Fin 2) ℝ N :=
  ⟨zernikeAnnulus hq ha hb (d.1 0+d.1 1) (d.1 1),
    (mem_restrictTotalDegree (Fin 2) N _).mpr
      ((totalDegree_zernikeAnnulus_le hq ha hb (by omega)).trans
        (by simpa only [sum_exponents_fin_two] using d.2))⟩

/-- All valid triangular Zernike polynomials are linearly independent. -/
theorem zernikeAnnulus_linearIndependent {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1 < a) (hb : -1 < b) :
    LinearIndependent ℝ (fun i : Σ n : ℕ, Fin (n+1) ↦ zernikeAnnulus hq ha hb i.1 i.2) := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := integralBilinForm (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b)
      (hasFiniteMoments_zernikeAnnulusMeasure hq ha hb))
  · intro i j hij
    apply integralInner_zernikeAnnulus_eq_zero hq ha hb (by omega) (by omega)
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
    change integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) _ _) ≠ 0
    rw [integralInner_self]
    exact (integral_sq_zernikeAnnulus_pos hq ha hb (by omega)).ne'

/-- Zernike polynomials form a basis of every complete finite total-degree space. -/
noncomputable def zernikeAnnulusDegreeBasis {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1 < a) (hb : -1 < b) (N : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := by
  classical
  let bmonomial : Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := basisRestrictSupport ℝ _
  have := Module.Finite.finite_basis bmonomial
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}
  have h := ((zernikeAnnulus_linearIndependent hq ha hb).comp _ diskIndex_injective).comp
    (fun d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ↦ d.1) Subtype.val_injective
  exact basisOfLinearIndependentOfCardEqFinrank' (zernikeAnnulusDegreeFamily hq ha hb N)
    (LinearIndependent.of_comp (restrictTotalDegree (Fin 2) ℝ N).subtype h)
    (Module.finrank_eq_card_basis bmonomial).symm

/-- The finite basis uses the semiclassical normalization and the real degree ordering. -/
@[simp] theorem zernikeAnnulusDegreeBasis_apply {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1 < a) (hb : -1 < b) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (zernikeAnnulusDegreeBasis hq ha hb N d : MvPolynomial (Fin 2) ℝ) =
      zernikeAnnulus hq ha hb (d.1 0+d.1 1) (d.1 1) := by
  simp [zernikeAnnulusDegreeBasis, zernikeAnnulusDegreeFamily]

end MvPolynomial
