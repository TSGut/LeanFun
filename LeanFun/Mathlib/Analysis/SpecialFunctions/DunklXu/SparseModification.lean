/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.ModificationExamples

/-!
# Six- and nine-position disk connection bounds

Every complete total-degree section has the asserted support. The bounds are
containments; some permitted entries can vanish too. The degree cutoff N here
includes degrees 0 through N, so the number of blocks is N+1.
Reference: separated Cartesian modification and Cholesky measure conversion.
-/

@[expose] public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- The normalized connection for multiplication of the disk weight by x²y². -/
noncomputable def dunklXuXYConnection {β : ℝ} (hβ : -1 < β) (N : ℕ) :
    Matrix {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
      {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ :=
  dunklXuModifiedConnection hβ (Polynomial.X^2) (Polynomial.X^2) 1
    (Filter.Eventually.of_forall (by intro x; simpa using sq_nonneg x))
    (Filter.Eventually.of_forall (by intro x; simpa using sq_nonneg x)) (by simpa only using dunklXuXYSystem hβ) N

/-- The normalized connection for the product of the two disk boundary quadratics. -/
noncomputable def dunklXuBoundaryProductConnection {β : ℝ} (hβ : -1 < β) (N : ℕ) :
    Matrix {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
      {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ :=
  dunklXuModifiedConnection hβ 1 diskBoundaryProductFactor 2
    (Filter.Eventually.of_forall (by intro x; simp))
    ((ae_mem_Icc_jacobiMeasure β β).mono (fun _ hx => diskBoundaryProductFactor_nonneg hx))
    (by simpa only using dunklXuBoundaryProductSystem hβ) N

/-- The x²y² connection has at most the six indicated positions in each column. -/
theorem dunklXuXYConnection_eq_zero {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N})
    (hout : ¬ ((j.1 0+j.1 1=i.1 0+i.1 1 ∨ j.1 0+j.1 1=i.1 0+i.1 1+2 ∨
        j.1 0+j.1 1=i.1 0+i.1 1+4) ∧ (j.1 1=i.1 1 ∨ j.1 1=i.1 1+2))) :
    dunklXuXYConnection hβ N i j = 0 := by
  unfold dunklXuXYConnection
  apply dunklXuModifiedConnection_eq_zero_of_outside_rectangle hβ (Polynomial.X^2)
    (Polynomial.X^2) 1 _ _ _
    (pow_ne_zero _ Polynomial.X_ne_zero) (by intro x; simp) (by intro x; simp)
    1 (by simp) (by simp) N i j
  rintro ⟨s,r,hs,hr,hn,hk⟩
  apply hout
  constructor <;> omega

/-- The boundary-product connection has at most nine indicated positions per column. -/
theorem dunklXuBoundaryProductConnection_eq_zero {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N})
    (hout : ¬ ((j.1 0+j.1 1=i.1 0+i.1 1 ∨ j.1 0+j.1 1=i.1 0+i.1 1+2 ∨
        j.1 0+j.1 1=i.1 0+i.1 1+4) ∧
      (j.1 1=i.1 1 ∨ j.1 1=i.1 1+2 ∨ j.1 1=i.1 1+4))) :
    dunklXuBoundaryProductConnection hβ N i j = 0 := by
  unfold dunklXuBoundaryProductConnection
  apply dunklXuModifiedConnection_eq_zero_of_outside_rectangle hβ 1 diskBoundaryProductFactor 2
    _ _ _ one_ne_zero (by intro x; simp)
    diskBoundaryProductFactor_even 0 (by simp) natDegree_diskBoundaryProductFactor_le N i j
  rintro ⟨s,r,hs,hr,hn,hk⟩
  apply hout
  constructor <;> omega

/-- Positive diagonal for the six-position connection. -/
theorem dunklXuXYConnection_diag_pos {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (i : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    0 < dunklXuXYConnection hβ N i i :=
  dunklXuModifiedConnection_diag_pos hβ _ _ _ _ _ _ N i

/-- Positive diagonal for the nine-position connection. -/
theorem dunklXuBoundaryProductConnection_diag_pos {β : ℝ} (hβ : -1 < β) (N : ℕ)
    (i : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    0 < dunklXuBoundaryProductConnection hβ N i i :=
  dunklXuModifiedConnection_diag_pos hβ _ _ _ _ _ _ N i

end MvPolynomial
