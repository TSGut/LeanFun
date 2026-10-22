/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticSupport
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Normalization

/-! # Quadratic modification entries in the normalized disk basis
The perturbation C*y²-B*(1-x²) is the one obtained from the disk deformation.
Its maximal inner-index entries do not depend on B. Positive norm scaling
preserves every zero and strict sign established for raw polynomial pairings.
Reference: Gutleb--Olver--Slevinsky, measure modification; Dunkl--Xu disk families.
-/

@[expose] public section
open Polynomial
namespace MvPolynomial

/-- The normalized quadratic perturbation matrix; its entries are symmetric pairings. -/
noncomputable def dunklXuQuadraticMatrix {β : ℝ} (hβ : -1 < β) (b c : ℝ) :
    Matrix (Σ n : ℕ, Fin (n + 1)) (Σ n : ℕ, Fin (n + 1)) ℝ := fun i j ↦
  integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) ((C c * X 1 ^ 2 - C b * (1 - X 0 ^ 2)) * normalizedDunklXuBasis hβ i) (normalizedDunklXuBasis hβ j))

/-- Positive norm scaling relates a normalized multiplication entry to its raw pairing. -/
theorem integralInner_mul_normalizedDunklXuBasis {β : ℝ} (hβ : -1 < β)
    (u : MvPolynomial (Fin 2) ℝ) (i j : Σ n : ℕ, Fin (n + 1)) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (u * normalizedDunklXuBasis hβ i) (normalizedDunklXuBasis hβ j)) =
      (dunklXuNorm β ⟨(i.1, i.2), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩)⁻¹ * (dunklXuNorm β ⟨(j.1, j.2), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩)⁻¹ *
        integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (u * dunklXuDisk β i.1 i.2) (dunklXuDisk β j.1 j.2)) := by
  simp only [normalizedDunklXuBasis_apply, mul_smul_comm]
  rw [integralInner_smul_left (h := (hasFiniteMoments_dunklXuDiskMeasure hβ).integrable_mul _ _), integralInner_comm,
    integralInner_smul_left (h := (hasFiniteMoments_dunklXuDiskMeasure hβ).integrable_mul _ _), integralInner_comm]
  ring

/-- The matrix is symmetric because multiplication is symmetric for the integral pairing. -/
theorem dunklXuQuadraticMatrix_symm {β : ℝ} (hβ : -1 < β) (b c : ℝ)
    (i j : Σ n : ℕ, Fin (n + 1)) :
    dunklXuQuadraticMatrix hβ b c i j = dunklXuQuadraticMatrix hβ b c j i := by
  unfold dunklXuQuadraticMatrix
  rw [integralInner_mul_left_right, integralInner_comm]

/-- Across different inner indices the outer-coordinate part vanishes exactly. -/
theorem dunklXuQuadraticMatrix_of_inner_ne {β : ℝ} (hβ : -1 < β) (b c : ℝ)
    (i j : Σ n : ℕ, Fin (n + 1)) (hij : (i.2 : ℕ) ≠ (j.2 : ℕ)) :
    dunklXuQuadraticMatrix hβ b c i j =
      c * ((dunklXuNorm β ⟨(i.1, i.2), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩)⁻¹ * (dunklXuNorm β ⟨(j.1, j.2), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩)⁻¹) *
        integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (X 1 ^ 2 * dunklXuDisk β i.1 i.2) (dunklXuDisk β j.1 j.2)) := by
  rw [dunklXuQuadraticMatrix, integralInner_mul_normalizedDunklXuBasis]
  simp only [sub_mul]
  rw [integralInner_sub_left (hasFiniteMoments_dunklXuDiskMeasure hβ)]
  have he : C b * (1 - X 0 ^ 2) =
      (Polynomial.C b * (1 - Polynomial.X ^ 2)).eval₂ C (X 0 : MvPolynomial (Fin 2) ℝ) := by
    simp
  simp only [he]
  rw [integralInner_outer_mul_dunklXuDisk_eq_zero hβ _ _ _ _ _ hij, sub_zero]
  have hs : C c * X 1 ^ 2 * dunklXuDisk β i.1 i.2 =
    c • (X 1 ^ 2 * dunklXuDisk β i.1 i.2) := by rw [smul_eq_C_mul, mul_assoc]
  simp only [hs]
  rw [integralInner_smul_left (h := (hasFiniteMoments_dunklXuDiskMeasure hβ).integrable_mul _ _)]
  ring

/-- The upward inner bandwidth is two, independently of the outer-coordinate coefficient. -/
theorem dunklXuQuadraticMatrix_eq_zero_of_inner_gap {β : ℝ} (hβ : -1 < β) (b c : ℝ)
    (i j : Σ n : ℕ, Fin (n + 1)) (hij : (i.2 : ℕ) + 2 < (j.2 : ℕ)) :
    dunklXuQuadraticMatrix hβ b c i j = 0 := by
  rw [dunklXuQuadraticMatrix_of_inner_ne hβ b c i j (by omega),
    integralInner_y_sq_dunklXuDisk_eq_zero_of_inner_gap hβ _ _ _ _ hij, mul_zero]

/-- Opposite inner parities do not couple in the quadratic modification. -/
theorem dunklXuQuadraticMatrix_eq_zero_of_inner_parity {β : ℝ} (hβ : -1 < β) (b c : ℝ)
    (i j : Σ n : ℕ, Fin (n + 1)) (hij : (i.2 : ℕ) % 2 ≠ (j.2 : ℕ) % 2) :
    dunklXuQuadraticMatrix hβ b c i j = 0 := by
  rw [dunklXuQuadraticMatrix_of_inner_ne hβ b c i j (by omega),
    integralInner_y_sq_dunklXuDisk_eq_zero_of_inner_parity hβ _ _ _ _ hij, mul_zero]

end MvPolynomial
