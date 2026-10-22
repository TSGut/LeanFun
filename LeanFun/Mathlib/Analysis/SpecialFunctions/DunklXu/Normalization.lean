/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Basis
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Positive normalization of the Cartesian disk basis

The normalization is by the positive square root of the product Jacobi norm.
It preserves degree/inner-index ordering and all connection-matrix zeros.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, disk families.
-/

@[expose] public section
open MeasureTheory Module
namespace MvPolynomial

/-- The finite norm of a square-integrable Cartesian disk polynomial. -/
noncomputable def dunklXuNorm (β : ℝ)
    (i : {i : ℕ × ℕ // Integrable (fun v ↦ eval v (dunklXuDisk β i.1 i.2)^2)
      (dunklXuDiskMeasure β)}) : ℝ :=
  Real.sqrt (∫ v, eval v (dunklXuDisk β i.val.1 i.val.2)^2 ∂dunklXuDiskMeasure β)

/-- The classical polynomial norm is nonnegative. -/
theorem dunklXuNorm_nonneg (β : ℝ)
    (i : {i : ℕ × ℕ // Integrable (fun v ↦ eval v (dunklXuDisk β i.1 i.2)^2)
      (dunklXuDiskMeasure β)}) : 0 ≤ dunklXuNorm β i :=
  Real.sqrt_nonneg _

/-- Its square is the classically convergent squared-polynomial integral. -/
theorem dunklXuNorm_sq (β : ℝ)
    (i : {i : ℕ × ℕ // Integrable (fun v ↦ eval v (dunklXuDisk β i.1 i.2)^2)
      (dunklXuDiskMeasure β)}) :
    dunklXuNorm β i ^ 2 = ∫ v, eval v (dunklXuDisk β i.val.1 i.val.2)^2
      ∂dunklXuDiskMeasure β :=
  Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))

/-- Disk norms are positive throughout the orthogonality range. -/
theorem dunklXuNorm_pos {β : ℝ} (hβ : -1 < β) (n k : ℕ) :
    0 < dunklXuNorm β ⟨(n, k), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩ :=
  Real.sqrt_pos.mpr (integral_sq_dunklXuDisk_pos hβ n k)

/-- Positive rescaling of the full disk basis gives the normalized basis. -/
noncomputable def normalizedDunklXuBasis {β : ℝ} (hβ : -1 < β) :
    Basis (Σ n : ℕ, Fin (n + 1)) ℝ (MvPolynomial (Fin 2) ℝ) :=
  (dunklXuBasis hβ).isUnitSMul
    (fun i => isUnit_iff_ne_zero.mpr (inv_ne_zero (dunklXuNorm_pos hβ i.1 i.2).ne'))

/-- The normalized basis uses positive inverse square roots of the squared norms. -/
@[simp] theorem normalizedDunklXuBasis_apply {β : ℝ} (hβ : -1 < β)
    (i : Σ n : ℕ, Fin (n + 1)) :
    normalizedDunklXuBasis hβ i = (dunklXuNorm β ⟨(i.1, i.2), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩)⁻¹ • dunklXuDisk β i.1 i.2 := by
  rw [normalizedDunklXuBasis, Basis.isUnitSMul_apply, dunklXuBasis_apply]

/-- The normalized disk basis is orthonormal for the integral pairing. -/
theorem integralInner_normalizedDunklXuBasis {β : ℝ} (hβ : -1 < β)
    (i j : Σ n : ℕ, Fin (n + 1)) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (normalizedDunklXuBasis hβ i) (normalizedDunklXuBasis hβ j)) = if i = j then 1 else 0 := by
  classical
  have hM := hasFiniteMoments_dunklXuDiskMeasure hβ
  have he := congrArg₂ (fun p q => integralInner (dunklXuDiskMeasure β) (hM.pair p q))
    (normalizedDunklXuBasis_apply hβ i) (normalizedDunklXuBasis_apply hβ j)
  rw [he, integralInner_smul_left (h := hM.integrable_mul _ _), integralInner_comm,
    integralInner_smul_left (h := hM.integrable_mul _ _), integralInner_comm]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, integralInner_self]
    have hp := integral_sq_dunklXuDisk_pos hβ i.1 i.2
    have hs := Real.sq_sqrt hp.le
    have hn := (Real.sqrt_pos.mpr hp).ne'
    dsimp [dunklXuNorm]
    field_simp
    nlinarith
  · rw [ite_eq_right hij]
    have ho : integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (dunklXuDisk β i.1 i.2) (dunklXuDisk β j.1 j.2)) = 0 := by
      apply integral_mul_dunklXuDisk_eq_zero hβ (by omega) (by omega)
      intro h
      apply hij
      have hn := congrArg Prod.fst h
      have hk := congrArg Prod.snd h
      rcases i with ⟨n, k⟩
      rcases j with ⟨m, l⟩
      dsimp at hn hk
      subst m
      congr 1
      exact Fin.ext hk
    rw [ho]
    ring

/-- Normalization changes coordinates by a positive row scaling. -/
theorem normalizedDunklXuBasis_repr {β : ℝ} (hβ : -1 < β)
    (p : MvPolynomial (Fin 2) ℝ) (i : Σ n : ℕ, Fin (n + 1)) :
    (normalizedDunklXuBasis hβ).repr p i =
      dunklXuNorm β ⟨(i.1, i.2), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩ * (dunklXuBasis hβ).repr p i := by
  rw [normalizedDunklXuBasis, Basis.repr_isUnitSMul]
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, inv_inv, smul_eq_mul]

/-- Positive normalization in a finite degree space. -/
noncomputable def normalizedDunklXuDegreeBasis {β : ℝ} (hβ : -1 < β) (N : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) :=
  (dunklXuDegreeBasis hβ N).isUnitSMul (fun d => isUnit_iff_ne_zero.mpr
    (inv_ne_zero (dunklXuNorm_pos hβ (d.1 0 + d.1 1) (d.1 1)).ne'))

/-- Finite and infinite normalized bases use exactly the same polynomials. -/
@[simp] theorem normalizedDunklXuDegreeBasis_apply {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    (normalizedDunklXuDegreeBasis hβ N d : MvPolynomial (Fin 2) ℝ) =
      normalizedDunklXuBasis hβ ⟨d.1 0 + d.1 1, ⟨d.1 1, by omega⟩⟩ := by
  rw [normalizedDunklXuDegreeBasis, Basis.isUnitSMul_apply,
    Submodule.coe_smul, dunklXuDegreeBasis_apply, normalizedDunklXuBasis_apply]

/-- Coordinates in the full normalized basis are polynomial integral pairings. -/
theorem normalizedDunklXuBasis_repr_eq_integralInner {β : ℝ} (hβ : -1 < β)
    (p : MvPolynomial (Fin 2) ℝ) (i : Σ n : ℕ, Fin (n + 1)) :
    (normalizedDunklXuBasis hβ).repr p i =
      integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (normalizedDunklXuBasis hβ i) p) := by
  classical
  have hL : (normalizedDunklXuBasis hβ).coord i =
      integralBilinForm (dunklXuDiskMeasure β) (hasFiniteMoments_dunklXuDiskMeasure hβ)
        (normalizedDunklXuBasis hβ i) := by
    apply (normalizedDunklXuBasis hβ).ext
    intro j
    change (normalizedDunklXuBasis hβ).repr (normalizedDunklXuBasis hβ j) i =
      integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (normalizedDunklXuBasis hβ i) (normalizedDunklXuBasis hβ j))
    rw [Module.Basis.repr_self, integralInner_normalizedDunklXuBasis]
    simp [Finsupp.single_apply, eq_comm]
  exact congrArg (fun L => L p) hL

end MvPolynomial
