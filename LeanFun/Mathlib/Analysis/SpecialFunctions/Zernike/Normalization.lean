/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Basis
public import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic.FieldSimp

/-! # Positively normalized finite Zernike bases
The real basis has the degree ordering used by MultivariateOrthogonalPolynomials.jl.
Its Gram matrix is the identity for the standard radial disk weight.
-/

@[expose] public section
open MeasureTheory Module
namespace MvPolynomial

/-- Positive standard norm in total-degree order. -/
noncomputable def zernikeNorm (a b : ℝ)
    (i : {i : ℕ × ℕ // Integrable (fun v ↦ eval v (zernike a b i.1 i.2)^2)
      (zernikeMeasure a b)}) : ℝ :=
  Real.sqrt (∫ v, eval v (zernike a b i.val.1 i.val.2)^2 ∂zernikeMeasure a b)

/-- The classical polynomial norm is nonnegative. -/
theorem zernikeNorm_nonneg (a b : ℝ)
    (i : {i : ℕ × ℕ // Integrable (fun v ↦ eval v (zernike a b i.1 i.2)^2)
      (zernikeMeasure a b)}) : 0 ≤ zernikeNorm a b i :=
  Real.sqrt_nonneg _

/-- Its square is the classically convergent squared-polynomial integral. -/
theorem zernikeNorm_sq (a b : ℝ)
    (i : {i : ℕ × ℕ // Integrable (fun v ↦ eval v (zernike a b i.1 i.2)^2)
      (zernikeMeasure a b)}) :
    zernikeNorm a b i ^ 2 = ∫ v, eval v (zernike a b i.val.1 i.val.2)^2
      ∂zernikeMeasure a b :=
  Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))

/-- Every valid index has positive norm. -/
theorem zernikeNorm_pos {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n j : ℕ} (hj : j≤n) : 0 < zernikeNorm a b ⟨(n, j), by exact hasFiniteMoments_zernikeMeasure (by linarith) (by linarith) _⟩ :=
  Real.sqrt_pos.mpr (integral_sq_zernike_pos ha hb hj)

/-- Complete finite bases with positive unit-norm scaling. -/
noncomputable def normalizedZernikeDegreeBasis {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) :=
  (zernikeDegreeBasis ha hb N).isUnitSMul (fun d ↦ isUnit_iff_ne_zero.mpr
    (inv_ne_zero (zernikeNorm_pos ha hb (show d.1 1 ≤ d.1 0+d.1 1 by omega)).ne'))

/-- The finite basis retains the real angular phase and divides by the positive norm. -/
@[simp] theorem normalizedZernikeDegreeBasis_apply {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (normalizedZernikeDegreeBasis ha hb N d : MvPolynomial (Fin 2) ℝ) =
      (zernikeNorm a b ⟨((d.1 0+d.1 1), (d.1 1)), by exact hasFiniteMoments_zernikeMeasure (by linarith) (by linarith) _⟩)⁻¹ • zernike a b (d.1 0+d.1 1) (d.1 1) := by
  rw [normalizedZernikeDegreeBasis, Basis.isUnitSMul_apply, Submodule.coe_smul,
    zernikeDegreeBasis_apply]

/-- The normalized finite basis has identity Gram matrix in the standard disk measure. -/
theorem integralGram_normalizedZernikeDegreeBasis {a b : ℝ}
    (ha : -1<a) (hb : -1<b) (N : ℕ) :
    integralGram (zernikeMeasure a b)
      (fun d ↦ (normalizedZernikeDegreeBasis ha hb N d : MvPolynomial (Fin 2) ℝ)) = 1 := by
  classical
  ext i j
  simp only [integralGram, normalizedZernikeDegreeBasis_apply, Matrix.one_apply]
  rw [integralInner_smul_left (h := (hasFiniteMoments_zernikeMeasure ha hb).integrable_mul _ _), integralInner_comm, integralInner_smul_left (h := (hasFiniteMoments_zernikeMeasure ha hb).integrable_mul _ _), integralInner_comm]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl, integralInner_self]
    have hp := integral_sq_zernike_pos ha hb (show i.1 1 ≤ i.1 0+i.1 1 by omega)
    have hs := Real.sq_sqrt hp.le
    have hn := (Real.sqrt_pos.mpr hp).ne'
    dsimp [zernikeNorm]
    field_simp
    nlinarith
  · rw [ite_eq_right hij, integralInner_zernike_eq_zero ha hb (by omega) (by omega),
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
