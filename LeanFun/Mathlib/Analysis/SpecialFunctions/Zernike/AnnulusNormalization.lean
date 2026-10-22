/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusBasis
public import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic.FieldSimp

/-! # Positively normalized finite Zernike annular bases
The real basis has the degree ordering used by MultivariateOrthogonalPolynomials.jl.
Its Gram matrix is the identity for the standard annular weight.
-/

@[expose] public section
open MeasureTheory Module Set
namespace MvPolynomial

/-- Positive standard norm in total-degree order. -/
noncomputable def zernikeAnnulusNorm {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (n j : ℕ) : ℝ :=
  Real.sqrt (∫ v, (eval v (zernikeAnnulus hq ha hb n j))^2 ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b)

/-- Every valid index has positive norm. -/
theorem zernikeAnnulusNorm_pos {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (ha : -1<a) (hb : -1<b)
    {n j : ℕ} (hj : j≤n) : 0 < zernikeAnnulusNorm hq ha hb n j :=
  Real.sqrt_pos.mpr (integral_sq_zernikeAnnulus_pos hq ha hb hj)

/-- Complete finite bases with positive unit-norm scaling. -/
noncomputable def normalizedZernikeAnnulusDegreeBasis {q a b : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ha : -1<a) (hb : -1<b) (N : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) :=
  (zernikeAnnulusDegreeBasis hq ha hb N).isUnitSMul (fun d ↦ isUnit_iff_ne_zero.mpr
    (inv_ne_zero (zernikeAnnulusNorm_pos hq ha hb (show d.1 1 ≤ d.1 0+d.1 1 by omega)).ne'))

/-- The finite basis retains the real angular phase and divides by the positive norm. -/
@[simp] theorem normalizedZernikeAnnulusDegreeBasis_apply {q a b : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ha : -1<a) (hb : -1<b) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (normalizedZernikeAnnulusDegreeBasis hq ha hb N d : MvPolynomial (Fin 2) ℝ) =
      (zernikeAnnulusNorm hq ha hb (d.1 0+d.1 1) (d.1 1))⁻¹ •
        zernikeAnnulus hq ha hb (d.1 0+d.1 1) (d.1 1) := by
  rw [normalizedZernikeAnnulusDegreeBasis, Basis.isUnitSMul_apply, Submodule.coe_smul,
    zernikeAnnulusDegreeBasis_apply]

/-- The normalized finite basis has identity Gram matrix in the standard annular measure. -/
theorem integralGram_normalizedZernikeAnnulusDegreeBasis {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (N : ℕ) :
    integralGram (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b)
      (fun d ↦ (normalizedZernikeAnnulusDegreeBasis hq ha hb N d : MvPolynomial (Fin 2) ℝ)) = 1 := by
  classical
  ext i j
  simp only [integralGram, normalizedZernikeAnnulusDegreeBasis_apply, Matrix.one_apply]
  rw [integralInner_smul_left (h := (hasFiniteMoments_zernikeAnnulusMeasure hq ha hb).integrable_mul _ _), integralInner_comm, integralInner_smul_left (h := (hasFiniteMoments_zernikeAnnulusMeasure hq ha hb).integrable_mul _ _), integralInner_comm]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl, integralInner_self]
    have hp := integral_sq_zernikeAnnulus_pos hq ha hb (show i.1 1 ≤ i.1 0+i.1 1 by omega)
    have hs := Real.sq_sqrt hp.le
    have hn := (Real.sqrt_pos.mpr hp).ne'
    dsimp [zernikeAnnulusNorm]
    field_simp
    nlinarith
  · rw [ite_eq_right hij, integralInner_zernikeAnnulus_eq_zero hq ha hb (by omega) (by omega),
      mul_zero, mul_zero]
    intro he
    apply hij
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have h0 := congrArg Prod.fst he
    have h1 := congrArg Prod.snd he
    fin_cases k <;> dsimp at h0 h1 ⊢ <;> omega

end MvPolynomial
