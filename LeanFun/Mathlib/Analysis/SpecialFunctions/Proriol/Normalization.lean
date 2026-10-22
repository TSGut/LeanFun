/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Coordinates
public import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic.FieldSimp

/-! # Positive normalization of finite Proriol bases
Divide each standard polynomial by its positive L2 norm. Reference: DLMF 18.37.8
and the orthonormal convention for Cholesky measure conversion.
-/

@[expose] public section
open MeasureTheory Module
namespace MvPolynomial

/-- The positive square root of the Proriol squared norm. -/
noncomputable def proriolNorm (α β γ : ℝ)
    (i : {i : ℕ × ℕ // Integrable (fun v ↦ eval v (proriol α β γ i.1 i.2)^2)
      (proriolMeasure α β γ)}) : ℝ :=
  Real.sqrt (∫ v, eval v (proriol α β γ i.val.1 i.val.2)^2 ∂proriolMeasure α β γ)

/-- The classical polynomial norm is nonnegative. -/
theorem proriolNorm_nonneg (α β γ : ℝ)
    (i : {i : ℕ × ℕ // Integrable (fun v ↦ eval v (proriol α β γ i.1 i.2)^2)
      (proriolMeasure α β γ)}) : 0 ≤ proriolNorm α β γ i :=
  Real.sqrt_nonneg _

/-- Its square is the classically convergent squared-polynomial integral. -/
theorem proriolNorm_sq (α β γ : ℝ)
    (i : {i : ℕ × ℕ // Integrable (fun v ↦ eval v (proriol α β γ i.1 i.2)^2)
      (proriolMeasure α β γ)}) :
    proriolNorm α β γ i ^ 2 = ∫ v, eval v (proriol α β γ i.val.1 i.val.2)^2
      ∂proriolMeasure α β γ :=
  Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))

/-- Norms are positive in the full admissible parameter range. -/
theorem proriolNorm_pos {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (n k : ℕ) :
    0 < proriolNorm α β γ ⟨(n, k), by exact hasFiniteMoments_proriolMeasure (by linarith) (by linarith) (by linarith) _⟩ := Real.sqrt_pos.mpr (integral_sq_proriolMeasure_pos hα hβ hγ n k)

/-- The complete degree basis rescaled by positive inverse norms. -/
noncomputable def normalizedProriolDegreeBasis {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) :=
  (proriolDegreeBasis hα hβ hγ N).isUnitSMul (fun d ↦ isUnit_iff_ne_zero.mpr
    (inv_ne_zero (proriolNorm_pos hα hβ hγ (d.1 0+d.1 1) (d.1 1)).ne'))

@[simp] theorem normalizedProriolDegreeBasis_apply {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (normalizedProriolDegreeBasis hα hβ hγ N d : MvPolynomial (Fin 2) ℝ) =
      (proriolNorm α β γ ⟨((d.1 0+d.1 1), (d.1 1)), by exact hasFiniteMoments_proriolMeasure (by linarith) (by linarith) (by linarith) _⟩)⁻¹ •
        proriol α β γ (d.1 0+d.1 1) (d.1 1) := by
  rw [normalizedProriolDegreeBasis, Basis.isUnitSMul_apply, Submodule.coe_smul,
    proriolDegreeBasis_apply]

/-- Normalized coordinates are raw coordinates multiplied by the target norm. -/
theorem normalizedProriolDegreeBasis_repr {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ)
    (p : restrictTotalDegree (Fin 2) ℝ N)
    (i : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    (normalizedProriolDegreeBasis hα hβ hγ N).repr p i =
      proriolNorm α β γ ⟨((i.1 0+i.1 1), (i.1 1)), by exact hasFiniteMoments_proriolMeasure (by linarith) (by linarith) (by linarith) _⟩ *
        (proriolDegreeBasis hα hβ hγ N).repr p i := by
  rw [normalizedProriolDegreeBasis, Basis.repr_isUnitSMul]
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, inv_inv, smul_eq_mul]

/-- The positive normalization has identity Gram matrix in the standard measure. -/
theorem integralGram_normalizedProriolDegreeBasis {α β γ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (N : ℕ) :
    integralGram (proriolMeasure α β γ)
      (fun i ↦ (normalizedProriolDegreeBasis hα hβ hγ N i : MvPolynomial (Fin 2) ℝ)) = 1 := by
  classical
  ext i j
  simp only [integralGram, normalizedProriolDegreeBasis_apply, Matrix.one_apply]
  rw [integralInner_smul_left (h := (hasFiniteMoments_proriolMeasure hα hβ hγ).integrable_mul _ _), integralInner_comm, integralInner_smul_left (h := (hasFiniteMoments_proriolMeasure hα hβ hγ).integrable_mul _ _), integralInner_comm]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl, integralInner_self]
    have hp := integral_sq_proriolMeasure_pos hα hβ hγ (i.1 0+i.1 1) (i.1 1)
    have hs := Real.sq_sqrt hp.le
    have hn := (Real.sqrt_pos.mpr hp).ne'
    dsimp [proriolNorm]
    field_simp
    nlinarith
  · rw [ite_eq_right hij]
    have ho := proriolDegreeBasis_orthogonal hα hβ hγ N i j hij
    simp only [proriolDegreeBasis_apply] at ho
    rw [ho, mul_zero, mul_zero]

end MvPolynomial
