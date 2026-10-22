/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Normalization

/-!
# Exact leading sections of raw Dunkl–Xu multiplication

Entries are full polynomial-basis coordinates before taking a leading section.
Diagonal norm scaling gives the normalized polynomial-modification Gram matrix.
This definition makes no unpadded truncated-product assertion.
Reference: Gutleb–Olver–Slevinsky, diagonal normalization and measure conversion.
-/

@[expose] public section
open Module Matrix
namespace MvPolynomial

/-- The leading degree-N section of multiplication in the raw Jacobi-normalized basis. -/
noncomputable def dunklXuMultiplicationSection {β : ℝ} (hβ : -1 < β)
    (u : MvPolynomial (Fin 2) ℝ) (N : ℕ) :
    Matrix {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
      {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ := fun i j =>
  (dunklXuBasis hβ).repr (u*dunklXuDisk β (j.1 0+j.1 1) (j.1 1))
    ⟨i.1 0+i.1 1,⟨i.1 1,by omega⟩⟩

/-- Norm scaling turns raw multiplication entries into normalized Gram entries. -/
theorem integralInner_mul_normalizedDunklXuDegreeBasis {β : ℝ} (hβ : -1 < β)
    (u : MvPolynomial (Fin 2) ℝ) (N : ℕ)
    (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    integralInner (dunklXuDiskMeasure β) (IntegrablePair.of (dunklXuDiskMeasure β) (u*(normalizedDunklXuDegreeBasis hβ N i : MvPolynomial (Fin 2) ℝ)) (normalizedDunklXuDegreeBasis hβ N j)) =
      dunklXuNorm β ⟨((i.1 0+i.1 1), (i.1 1)), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩ * dunklXuMultiplicationSection hβ u N i j *
        (dunklXuNorm β ⟨((j.1 0+j.1 1), (j.1 1)), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩)⁻¹ := by
  rw [integralInner_mul_left_right]
  simp only [normalizedDunklXuDegreeBasis_apply]
  rw [← normalizedDunklXuBasis_repr_eq_integralInner,
    normalizedDunklXuBasis_repr,normalizedDunklXuBasis_apply,
    mul_smul_comm,map_smul,Finsupp.smul_apply,smul_eq_mul]
  unfold dunklXuMultiplicationSection
  ring

end MvPolynomial
