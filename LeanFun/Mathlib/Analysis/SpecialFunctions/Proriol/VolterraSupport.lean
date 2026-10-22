/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraCoordinates
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.MeasureModification

/-! # Total-degree support for finite Volterra assembly

A kernel of total degree d has degree-block bandwidth d in Proriol coordinates.
The extension stays within one degree and the marginal selects that same degree.
Reference: Gutleb–Olver, Sections 3.1–3.2.
-/

public noncomputable section
open Polynomial
namespace MvPolynomial

/-- Reflection removes the simplex coordinate change from each synthesis column. -/
theorem triangleReflect_proriolVolterraSynthesis_single
    (i : Σ n : ℕ, Fin (n+1)) (a : ℝ) :
    triangleReflect (proriolVolterraSynthesis (Finsupp.single i a)) =
      (a * (-1 : ℝ)^(i.1-i.2.val)) • proriol 0 0 0 i.1 i.2 := by
  simp only [proriolVolterraSynthesis, Finsupp.linearCombination_single, map_smul,
    smul_smul]
  rw [triangleReflect_involutive]

/-- Orthogonality extracts one signed reflected coefficient. -/
theorem integralInner_reflect_proriolVolterraSynthesis
    (c : (Σ n : ℕ, Fin (n+1)) →₀ ℝ) (i : Σ n : ℕ, Fin (n+1)) :
    integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) (triangleReflect (proriolVolterraSynthesis c)) (proriol 0 0 0 i.1 i.2) (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) =
      c i * (-1 : ℝ)^(i.1-i.2.val) *
        integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) (proriol 0 0 0 i.1 i.2) (proriol 0 0 0 i.1 i.2) (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp [integralInner]
  | add c d hc hd =>
    simp only [map_add, Finsupp.add_apply,
      integralInner_add_left (hasFiniteMoments_proriolMeasure (α := 0) (β := 0) (γ := 0) (by norm_num) (by norm_num) (by norm_num)),
      hc, hd, add_mul]
  | single j a =>
    simp only [triangleReflect_proriolVolterraSynthesis_single]
    rw [integralInner_smul_left (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)]
    by_cases h : j = i
    · subst j
      simp
    · have hne : (j.1,j.2.val) ≠ (i.1,i.2.val) := by
        intro he
        apply h
        exact Sigma.ext (congrArg Prod.fst he)
          ((Fin.heq_ext_iff (congrArg (fun n : ℕ ↦ n+1) (congrArg Prod.fst he))).mpr
            (congrArg Prod.snd he))
      rw [integralInner_proriolMeasure_eq_zero (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) hne, mul_zero, Finsupp.single_eq_of_ne (Ne.symm h)]
      simp

/-- Multiplication by an arbitrary polynomial has total-degree block bandwidth
bounded by its total degree; no finite-section product is used. -/
theorem proriolKernelMap_entry_eq_zero (K : MvPolynomial (Fin 2) ℝ)
    (i j : Σ n : ℕ, Fin (n+1))
    (hgap : j.1 + K.totalDegree < i.1 ∨ i.1 + K.totalDegree < j.1) :
    proriolKernelMap K (Finsupp.single j 1) i = 0 := by
  have h := integralInner_reflect_proriolVolterraSynthesis
    (proriolKernelMap K (Finsupp.single j 1)) i
  simp only [proriolVolterraSynthesis_kernelMap, map_mul,
    triangleReflect_proriolVolterraSynthesis_single, one_mul, mul_smul_comm] at h
  rw [integralInner_smul_left (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)] at h
  have hz : integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) (K * proriol 0 0 0 j.1 j.2) (proriol 0 0 0 i.1 i.2) (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) = 0 := by
    rcases hgap with hgap | hgap
    · apply integralInner_proriolMeasure_eq_zero_of_totalDegree_lt
        (by norm_num) (by norm_num) (by norm_num) _ (by omega)
      exact (totalDegree_mul _ _).trans_lt
        ((Nat.add_le_add_left (totalDegree_proriol_le 0 0 0 (by omega)) _).trans_lt
          (by omega))
    · have he : integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) (K * proriol 0 0 0 j.1 j.2) (proriol 0 0 0 i.1 i.2) (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) =
        integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) (K * proriol 0 0 0 i.1 i.2) (proriol 0 0 0 j.1 j.2) (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) := by
        unfold integralInner
        congr 1
        funext x
        simp only [map_mul]
        ring
      rw [he]
      apply integralInner_proriolMeasure_eq_zero_of_totalDegree_lt
        (by norm_num) (by norm_num) (by norm_num) _ (by omega)
      exact (totalDegree_mul _ _).trans_lt
        ((Nat.add_le_add_left (totalDegree_proriol_le 0 0 0 (by omega)) _).trans_lt
          (by omega))
  have href := triangleReflect_involutive K
  dsimp only [integralInner, IntegrablePair.of] at h hz
  rw [href, hz, mul_zero] at h
  have hn : integralInner (proriolMeasure 0 0 0) (IntegrablePair.of (proriolMeasure 0 0 0) (proriol 0 0 0 i.1 i.2) (proriol 0 0 0 i.1 i.2) (h := (hasFiniteMoments_proriolMeasure (by norm_num) (by norm_num) (by norm_num)).integrable_mul _ _)) ≠ 0 := by
    rw [integralInner_self]
    exact (integral_sq_proriolMeasure_pos (by norm_num) (by norm_num) (by norm_num) _ _).ne'
  exact (mul_eq_zero.mp (mul_eq_zero.mp h.symm |>.resolve_right hn)).resolve_right
    (pow_ne_zero _ (by norm_num))

/-- A degree-d polynomial kernel gives bandwidth (d,d) before the explicit
endpoint factor and output reflection. -/
theorem volterraProriolCoefficients_entry_eq_zero (K : MvPolynomial (Fin 2) ℝ)
    (m n : ℕ) (hgap : n + K.totalDegree < m ∨ m + K.totalDegree < n) :
    volterraProriolCoefficients K (Finsupp.single n 1) m = 0 := by
  classical
  rw [volterraProriolCoefficients, LinearMap.comp_apply, LinearMap.comp_apply,
    proriolMarginalCoefficients_apply, proriolExtensionMap_single]
  let c := proriolExtensionCoefficients n (shiftedJacobi 1 0 n)
    (natDegree_shiftedJacobi_le 1 0 n)
  change proriolKernelMap K c ⟨m,0⟩ = 0
  conv_lhs => rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hn : i.1 = n := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hi)
      (proriolExtensionCoefficients_shiftedJacobi_eq_zero_of_degree_ne n i h)
  have hz := proriolKernelMap_entry_eq_zero K ⟨m,0⟩ i (by simpa [hn] using hgap)
  have hs : Finsupp.single i (c i) = (c i) • Finsupp.single i (1 : ℝ) := by simp
  rw [hs, map_smul, Finsupp.smul_apply, hz, smul_zero]

/-- Exact rectangular section: N input modes require at most N+d output modes
before the explicit endpoint factor. -/
def volterraProriolSection (K : MvPolynomial (Fin 2) ℝ) (N : ℕ) :
    Matrix (Fin (N + K.totalDegree)) (Fin N) ℝ :=
  fun i j ↦ volterraProriolCoefficients K (Finsupp.single j.val 1) i.val

/-- The finite section inherits the same two-sided bandwidth. -/
theorem volterraProriolSection_eq_zero (K : MvPolynomial (Fin 2) ℝ) (N : ℕ)
    (i : Fin (N + K.totalDegree)) (j : Fin N)
    (hgap : j.val + K.totalDegree < i.val ∨ i.val + K.totalDegree < j.val) :
    volterraProriolSection K N i j = 0 :=
  volterraProriolCoefficients_entry_eq_zero K i.val j.val hgap

/-- Matrix-vector multiplication in the rectangular section agrees with the
full finite-support operator at every retained row. -/
theorem volterraProriolSection_mulVec (K : MvPolynomial (Fin 2) ℝ) (N : ℕ)
    (v : Fin N → ℝ) (i : Fin (N + K.totalDegree)) :
    (volterraProriolSection K N).mulVec v i =
      volterraProriolCoefficients K (∑ j : Fin N, Finsupp.single j.val (v j)) i.val := by
  classical
  simp only [Matrix.mulVec, dotProduct, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [show Finsupp.single j.val (v j) = (v j) • Finsupp.single j.val (1 : ℝ) by simp,
    map_smul, Finsupp.smul_apply]
  simp only [volterraProriolSection, smul_eq_mul, mul_comm]

/-- No rows are lost by the rectangular cutoff for inputs supported below N. -/
theorem volterraProriolCoefficients_cutoff (K : MvPolynomial (Fin 2) ℝ)
    (N : ℕ) (c : ℕ →₀ ℝ) (hc : ∀ n ∈ c.support, n < N)
    (m : ℕ) (hm : N + K.totalDegree ≤ m) :
    volterraProriolCoefficients K c m = 0 := by
  classical
  conv_lhs => rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hz := volterraProriolCoefficients_entry_eq_zero K m n (Or.inl (by
    have := hc n hn
    omega))
  have hs : Finsupp.single n (c n) = (c n) • Finsupp.single n (1 : ℝ) := by simp
  rw [hs, map_smul, Finsupp.smul_apply, hz, smul_zero]

/-- Constant-kernel assembly recovers the established Jacobi diagonal exactly. -/
theorem volterraProriolCoefficients_one :
    volterraProriolCoefficients 1 = volterraJacobiDiagonal := by
  apply LinearMap.ext
  intro c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single n a =>
    have hs : Finsupp.single n a = a • Finsupp.single n (1 : ℝ) := by simp
    rw [hs, map_smul, map_smul]
    congr 1
    simp only [volterraProriolCoefficients, LinearMap.comp_apply, map_one,
      Module.End.one_apply, proriolExtensionMap_single,
      proriolMarginalCoefficients_extension_shiftedJacobi,
      volterraJacobiDiagonal_single, one_mul]

end MvPolynomial
