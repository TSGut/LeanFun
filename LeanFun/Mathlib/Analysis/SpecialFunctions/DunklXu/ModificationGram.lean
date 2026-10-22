/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.ModifiedConnection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.MultiplicationSection
public import LeanFun.Mathlib.LinearAlgebra.Matrix.CholeskyLU

/-!
# Modified disk Gram factors and raw multiplication sections

The normalized connection factors the diagonally conjugated raw multiplication
section. This is the exact algebra needed to interpret unpivoted LU sparsity.
Reference: Gutleb–Olver–Slevinsky, measure conversion by Cholesky factorization.
-/

public section
open MeasureTheory Set Polynomial Module Matrix
namespace MvPolynomial
variable {β : ℝ} (hβ : -1 < β) (h g : ℝ[X]) (l : ℕ)
    (hh : ∀ᵐ x ∂jacobiMeasure (β+1/2) (β+1/2), 0 ≤ h.eval x)
    (hg : ∀ᵐ z ∂jacobiMeasure β β, 0 ≤ g.eval z)
    (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure (g) (((jacobiMeasure β β)).comap Subtype.val)))

/-- The positive connection factor is upper triangular in degree then inner-index order. -/
theorem dunklXuModifiedConnection_eq_zero_of_order
    (hh0 : h ≠ 0) (hhpar : ∀ x, h.eval (-x) = h.eval x)
    (hgpar : ∀ z, g.eval (-z) = g.eval z) (hgdeg : g.natDegree ≤ 2*l)
    (N : ℕ) (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N})
    (hij : j.1 0+j.1 1 < i.1 0+i.1 1 ∨
      (j.1 0+j.1 1=i.1 0+i.1 1 ∧ j.1 1 < i.1 1)) :
    dunklXuModifiedConnection hβ h g l hh hg T N i j = 0 := by
  apply dunklXuModifiedConnection_eq_zero_of_outside_rectangle hβ h g l hh hg T
    hh0 hhpar hgpar h.natDegree (by omega) hgdeg N i j
  rintro ⟨s,r,hs,hr,hn,hk⟩
  omega

/-- The connection factors the raw multiplication section after diagonal norm conjugation. -/
theorem dunklXuModifiedConnection_transpose_mul
    (hgpar : ∀ z, g.eval (-z) = g.eval z) (hgdeg : g.natDegree ≤ 2*l)
    (N : ℕ) [Fintype {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}] :
    (dunklXuModifiedConnection hβ h g l hh hg T N).transpose *
        dunklXuModifiedConnection hβ h g l hh hg T N =
      diagonal (fun i => dunklXuNorm β ⟨((i.1 0+i.1 1), (i.1 1)), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩) *
        dunklXuMultiplicationSection hβ (cartesianDiskModification h g l) N *
      diagonal (fun i => (dunklXuNorm β ⟨((i.1 0+i.1 1), (i.1 1)), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩)⁻¹) := by
  classical
  have hgc : ∀ i, i % 2 ≠ 0 → g.coeff i = 0 := by
    intro i hi
    apply coeff_eq_zero_of_reflection 0 i _ hi
    apply Polynomial.funext
    intro z
    simpa using hgpar z
  rw [← integralGram_eq_dunklXuModifiedConnection_transpose_mul hβ h g l hh hg T N]
  ext i j
  simp only [diagonal_mul,mul_diagonal,integralGram]
  rw [integralInner_cartesianDiskModification
    (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith))
    (hasFiniteMoments_jacobiMeasure hβ hβ) (ae_mem_Icc_jacobiMeasure _ _)
    (ae_mem_Icc_jacobiMeasure _ _) h g l hh hg hgdeg hgc]
  exact integralInner_mul_normalizedDunklXuDegreeBasis hβ _ N i j

end MvPolynomial
