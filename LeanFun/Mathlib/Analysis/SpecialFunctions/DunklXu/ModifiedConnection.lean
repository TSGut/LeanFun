/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.CartesianSystem
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.GramFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.ModifiedSystem
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.ModificationDensity

/-!
# Sparse modified-measure connections from the Dunkl–Xu basis

The source is the existing normalized Dunkl–Xu basis, in total-degree blocks
with increasing inner index. Target systems exist by the nondegenerate
polynomial-density construction. All support bounds hold for every degree section.
Reference: Dunkl–Xu; Gutleb–Olver–Slevinsky, Cholesky measure conversion.
-/

@[expose] public section
open MeasureTheory Set Polynomial Module
namespace MvPolynomial
variable {β : ℝ} (hβ : -1 < β) (h g : ℝ[X]) (l : ℕ)
    (hh : ∀ᵐ x ∂jacobiMeasure (β+1/2) (β+1/2), 0 ≤ h.eval x)
    (hg : ∀ᵐ z ∂jacobiMeasure β β, 0 ≤ g.eval z)
    (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure (g) (((jacobiMeasure β β)).comap Subtype.val)))

/-- The finite conversion from the standard normalized Dunkl–Xu basis to the modified basis. -/
noncomputable def dunklXuModifiedConnection (N : ℕ) :
    Matrix {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
      {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ := by
  have hμ := hasFiniteMoments_jacobiMeasure (show -1 < β+1/2 by linarith)
    (show -1 < β+1/2 by linarith)
  let := (hμ.diskOuterModification (ae_mem_Icc_jacobiMeasure _ _) h hh l).isFiniteMeasure
  let := ((hasFiniteMoments_jacobiMeasure hβ hβ).polynomialDensityMeasure g hg).isFiniteMeasure
  exact (T.degreeBasis (ae_mem_diskOuterModification (ae_mem_Icc_jacobiMeasure _ _) h l)
    ((polynomialDensityMeasure_comap_absolutelyContinuous g (jacobiMeasure β β)).ae_le (ae_mem_Icc_jacobiMeasure β β)) N).toMatrix
      (normalizedDunklXuDegreeBasis hβ N)

/-- Entries agree with the general Cartesian connection, independently of its construction. -/
theorem dunklXuModifiedConnection_apply
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (jacobiMeasure (β+1/2) (β+1/2))) (jacobiMeasure β β))
    (N : ℕ) (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    dunklXuModifiedConnection hβ h g l hh hg T N i j =
      S.connectionEntry T (j.1 0+j.1 1) (j.1 1) (i.1 0+i.1 1) (i.1 1)
        (hi := (T.hasFiniteMoments (ae_mem_diskOuterModification (ae_mem_Icc_jacobiMeasure _ _) h l)).integrable_mul _ _) := by
  have hμ := hasFiniteMoments_jacobiMeasure (show -1 < β+1/2 by linarith)
    (show -1 < β+1/2 by linarith)
  let := (hμ.diskOuterModification (ae_mem_Icc_jacobiMeasure _ _) h hh l).isFiniteMeasure
  let := ((hasFiniteMoments_jacobiMeasure hβ hβ).polynomialDensityMeasure g hg).isFiniteMeasure
  have hx' : ∀ᵐ x ∂diskOuterModification h l ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val),
      x ∈ Icc (-1 : ℝ) 1 := ae_mem_diskOuterModification (ae_mem_Icc_jacobiMeasure _ _) h l
  have hz' : ∀ᵐ z ∂Polynomial.polynomialDensityMeasure (g) (((jacobiMeasure β β)).comap Subtype.val),
      z ∈ Icc (-1 : ℝ) 1 :=
    (polynomialDensityMeasure_comap_absolutelyContinuous g (jacobiMeasure β β)).ae_le (ae_mem_Icc_jacobiMeasure β β)
  change (T.degreeBasis hx' hz' N).repr (normalizedDunklXuDegreeBasis hβ N j) i = _
  rw [T.degreeBasis_repr hx' hz']
  simp only [normalizedDunklXuDegreeBasis_apply, normalizedDunklXuBasis_eq_cartesian hβ S]
  exact integralInner_comm _ _ _

/-- The normalized connection is an exact Gram factor for the modified disk measure. -/
theorem integralGram_eq_dunklXuModifiedConnection_transpose_mul (N : ℕ)
    [Fintype {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}] :
    integralGram (cartesianDiskMeasure
      (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val)))
      (ProductMeasureInput.ofSFinite (hν := by let := (hasFiniteMoments_jacobiMeasure hβ hβ).isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val))) (Polynomial.polynomialDensityMeasure (g) (((jacobiMeasure β β)).comap Subtype.val))))
      (fun i => (normalizedDunklXuDegreeBasis hβ N i : MvPolynomial (Fin 2) ℝ))
      (hP := fun _ _ => (T.hasFiniteMoments (ae_mem_diskOuterModification (ae_mem_Icc_jacobiMeasure _ _) h l)).integrable_mul _ _) =
      (dunklXuModifiedConnection hβ h g l hh hg T N).transpose *
        dunklXuModifiedConnection hβ h g l hh hg T N := by
  classical
  have hμ := hasFiniteMoments_jacobiMeasure (show -1 < β+1/2 by linarith)
    (show -1 < β+1/2 by linarith)
  let := (hμ.diskOuterModification (ae_mem_Icc_jacobiMeasure _ _) h hh l).isFiniteMeasure
  let := ((hasFiniteMoments_jacobiMeasure hβ hβ).polynomialDensityMeasure g hg).isFiniteMeasure
  have hx' := ae_mem_diskOuterModification (ae_mem_Icc_jacobiMeasure (β+1/2) (β+1/2)) h l
  have hz' := (polynomialDensityMeasure_comap_absolutelyContinuous g (jacobiMeasure β β)).ae_le (ae_mem_Icc_jacobiMeasure β β)
  exact integralGram_eq_transpose_toMatrix_mul _
    (hasFiniteMoments_cartesianDiskMeasure hx' hz') (T.hasPositiveDefiniteIntegral hx' hz')
    _ _ (T.integralGram_degreeBasis hx' hz' N)

/-- Every finite section has the same bounded rectangle of allowed even offsets. -/
theorem dunklXuModifiedConnection_eq_zero_of_outside_rectangle
    (hh0 : h ≠ 0) (hhpar : ∀ x, h.eval (-x) = h.eval x)
    (hgpar : ∀ z, g.eval (-z) = g.eval z) (a : ℕ)
    (hhdeg : h.natDegree ≤ 2*a) (hgdeg : g.natDegree ≤ 2*l)
    (N : ℕ) (i j : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N})
    (hout : ¬ ∃ s r : ℕ, s ≤ a+l ∧ r ≤ l ∧
      j.1 0+j.1 1=i.1 0+i.1 1+2*s ∧ j.1 1=i.1 1+2*r) :
    dunklXuModifiedConnection hβ h g l hh hg T N i j = 0 := by
  let := isNegInvariant_jacobiMeasure (β+1/2)
  let := isNegInvariant_jacobiMeasure β
  rw [dunklXuModifiedConnection_apply hβ h g l hh hg T (dunklXuCartesianSystem hβ)]
  exact (dunklXuCartesianSystem hβ).connectionEntry_eq_zero_of_outside_rectangle h g l T
    (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith))
    (hasFiniteMoments_jacobiMeasure hβ hβ) (ae_mem_Icc_jacobiMeasure _ _) hh hg
    (hasPositiveDefiniteIntegral_jacobiMeasure (by linarith) (by linarith)) hh0 hhpar hgpar
    a hhdeg hgdeg (by omega) (by omega) hout

/-- The same-index conversion coefficient is positive. -/
theorem dunklXuModifiedConnection_diag_pos (N : ℕ)
    (i : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    0 < dunklXuModifiedConnection hβ h g l hh hg T N i i := by
  rw [dunklXuModifiedConnection_apply hβ h g l hh hg T (dunklXuCartesianSystem hβ)]
  exact (dunklXuCartesianSystem hβ).connectionEntry_diag_pos h g l T
    (hasFiniteMoments_jacobiMeasure (by linarith) (by linarith))
    (hasFiniteMoments_jacobiMeasure hβ hβ) (ae_mem_Icc_jacobiMeasure _ _) hh hg _ _

end MvPolynomial
