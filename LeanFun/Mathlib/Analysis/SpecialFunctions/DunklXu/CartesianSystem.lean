/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.Normalization
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.DiskOuterMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.EvenMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.System

/-!
# Identification of the Cartesian and normalized Dunkl–Xu systems

The abstract positive-leading normalization agrees with the Jacobi-normalized
Dunkl–Xu family after division by its positive norm.
Reference: Dunkl–Xu, Cartesian disk polynomials; DLMF Table 18.3.1.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- The positive-leading Cartesian system for the standard radial disk weight. -/
@[expose] noncomputable def dunklXuCartesianSystem {β : ℝ} (hβ : -1 < β) :
    CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (jacobiMeasure (β+1/2) (β+1/2))) (jacobiMeasure β β) := by
  let := isNegInvariant_jacobiMeasure β
  have ha : -1 < β+1/2 := by linarith
  exact cartesianDiskSystem _ _ (hasFiniteMoments_jacobiMeasure ha ha)
    (hasPositiveDefiniteIntegral_jacobiMeasure ha ha)
    (hasFiniteMoments_jacobiMeasure hβ hβ) (hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ)
    (ae_mem_Icc_jacobiMeasure _ _)

/-- The raw Jacobi-normalized disk polynomial is a positive scalar multiple
of every positive-leading orthonormal Cartesian realization. -/
theorem dunklXuDisk_eq_pos_smul_cartesian {β : ℝ} (hβ : -1 < β)
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (jacobiMeasure (β+1/2) (β+1/2))) (jacobiMeasure β β))
    (n k : ℕ) : ∃ c : ℝ, 0 < c ∧ dunklXuDisk β n k = c • S.polynomial n k := by
  have ha : -1 < β+1/2 := by linarith
  have hak : -1 < (β+1/2)+(k : ℝ) := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  let J := jacobiSequence hβ hβ
  let K := jacobiSequence hak hak
  have hJ : J.IsOrthogonal (jacobiMeasure β β) := isOrthogonal_jacobiSequence hβ hβ
  have hK : K.IsOrthogonal (diskOuterMeasure k ((jacobiMeasure (β+1/2) (β+1/2)).comap Subtype.val)) :=
    isOrthogonal_jacobiSequence_diskOuterMeasure ha k
  have hjpos : 0 < (J k).leadingCoeff := by
    change 0 < (J k).coeff (J k).natDegree
    rw [J.natDegree_eq]
    exact coeff_jacobi_self_pos hβ hβ k
  have hkpos : 0 < (K (n-k)).leadingCoeff := by
    change 0 < (K (n-k)).coeff (K (n-k)).natDegree
    rw [K.natDegree_eq]
    exact coeff_jacobi_self_pos hak hak (n-k)
  let ci := (J k).leadingCoeff/(S.inner k).leadingCoeff
  let co := (K (n-k)).leadingCoeff/(S.outer k (n-k)).leadingCoeff
  have hi : jacobi β β k = ci • S.inner k :=
    S.inner_orthogonal.eq_leadingCoeff_div_smul
      (hasFiniteMoments_jacobiMeasure hβ hβ)
      (hasPositiveDefiniteIntegral_jacobiMeasure hβ hβ) hJ k
  have ho : jacobi ((β+1/2)+k) ((β+1/2)+k) (n-k) = co • S.outer k (n-k) :=
    (S.outer_orthogonal_real k (ae_mem_Icc_jacobiMeasure _ _)).eq_leadingCoeff_div_smul
      ((hasFiniteMoments_jacobiMeasure ha ha).diskOuterMeasure
        (ae_mem_Icc_jacobiMeasure _ _) k)
      ((hasPositiveDefiniteIntegral_jacobiMeasure ha ha).diskOuterMeasure
        (hasFiniteMoments_jacobiMeasure ha ha) (ae_mem_Icc_jacobiMeasure _ _) k) hK (n-k)
  refine ⟨co*ci,mul_pos (div_pos hkpos (S.outer_leadingCoeff_pos k (n-k)))
    (div_pos hjpos (S.inner_leadingCoeff_pos k)),?_⟩
  rw [dunklXuDisk,show β+(k : ℝ)+1/2=(β+1/2)+k by ring,ho,hi,diskLift_smul]
  simp only [Polynomial.smul_eq_C_mul,Polynomial.eval₂_mul,Polynomial.eval₂_C,
    CartesianDiskSystem.polynomial,cartesianDiskPolynomial,MvPolynomial.smul_eq_C_mul,map_mul]
  ring

/-- The standard normalized Dunkl–Xu basis equals the general Cartesian construction. -/
theorem normalizedDunklXuBasis_eq_cartesian {β : ℝ} (hβ : -1 < β)
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (jacobiMeasure (β+1/2) (β+1/2))) (jacobiMeasure β β))
    (i : Σ n : ℕ, Fin (n+1)) : normalizedDunklXuBasis hβ i = S.polynomial i.1 i.2 := by
  obtain ⟨c,hc,he⟩ := dunklXuDisk_eq_pos_smul_cartesian hβ S i.1 i.2
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isFiniteMeasure_jacobiMeasure (show -1 < β+1/2 by linarith)
    (show -1 < β+1/2 by linarith)
  have hn : ∫ v, eval v (S.polynomial i.1 i.2)^2 ∂dunklXuDiskMeasure β = 1 := by
    simpa only [integralInner,pow_two,cartesianDiskMeasure,dunklXuDiskMeasure] using
      S.integralInner_polynomial_self (ae_mem_Icc_jacobiMeasure _ _) i.1 i.2
  have hcN : dunklXuNorm β ⟨(i.1, i.2), by exact hasFiniteMoments_dunklXuDiskMeasure (by linarith) _⟩ = c := by
    rw [dunklXuNorm,he]
    simp only [MvPolynomial.smul_eq_C_mul,map_mul,eval_C,mul_pow,integral_const_mul,hn,mul_one]
    exact Real.sqrt_sq hc.le
  rw [normalizedDunklXuBasis_apply,hcN,he,smul_smul,inv_mul_cancel₀ hc.ne',one_smul]

end MvPolynomial
