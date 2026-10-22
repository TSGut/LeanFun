/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.Laurent

/-! # Finite boundary defects of Laurent-polynomial Toeplitz products

Reference: Böttcher–Silbermann, Introduction to Large Truncated Toeplitz
Matrices, Chapter 1. All boundary defects have finite coordinate range.
-/

@[expose] public noncomputable section
namespace lp
variable {𝕜 : Type*} [RCLike 𝕜]
local notation "H" => lp (fun _ : ℕ ↦ 𝕜) 2

/-- Forward shift powers act by translation above the boundary. -/
theorem forwardShiftL2_pow_apply (n : ℕ) (u : H) (i : ℕ) (h : n ≤ i) :
    (forwardShiftL2.toContinuousLinearMap ^ n) u i = u (i-n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    rw [pow_succ']
    change forwardShiftL2 ((forwardShiftL2.toContinuousLinearMap ^ n) u) (j+1) = _
    rw [forwardShiftL2_succ, ih j (by omega)]
    exact congrArg (fun j : ℕ ↦ u j) (by omega)

/-- Forward shift powers vanish below their first possible output coordinate. -/
theorem forwardShiftL2_pow_apply_of_lt (n : ℕ) (u : H) (i : ℕ) (h : i < n) :
    (forwardShiftL2.toContinuousLinearMap ^ n) u i = 0 := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [pow_succ']
    change forwardShiftL2 ((forwardShiftL2.toContinuousLinearMap ^ n) u) i = 0
    cases i with
    | zero => exact forwardShiftL2_zero _
    | succ i => exact ih i (by omega)

/-- Backward shift powers delete an initial segment. -/
theorem backwardShiftL2_pow_apply (n : ℕ) (u : H) (i : ℕ) :
    (backwardShiftL2 ^ n) u i = u (i+n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change backwardShiftL2 ((backwardShiftL2 ^ n) u) i = _
    rw [backwardShiftL2_apply, ih]
    exact congrArg (fun j : ℕ ↦ u j) (by omega)

/-- Away from the boundary, a signed shift is ordinary integer translation. -/
theorem laurentShiftL2_apply_of_le (k : ℤ) (u : H) (i : ℕ) (h : k ≤ (i : ℤ)) :
    laurentShiftL2 k u i = u ((i : ℤ)-k).toNat := by
  cases k with
  | ofNat n =>
    change (n : ℤ) ≤ (i : ℤ) at h
    rw [laurentShiftL2, forwardShiftL2_pow_apply n u i (by omega)]
    change u (i-n) = u ((i : ℤ)-(n : ℤ)).toNat
    exact congrArg (fun j : ℕ ↦ u j) (by omega)
  | negSucc n =>
    rw [laurentShiftL2, backwardShiftL2_pow_apply]
    congr 1

/-- The matrix of a signed shift is the indicator of its integer diagonal. -/
theorem laurentShiftL2_single_entry (k : ℤ) (i j : ℕ) :
    laurentShiftL2 (𝕜 := 𝕜) k (lp.single 2 j 1) i =
      if (i : ℤ)-j = k then 1 else 0 := by
  by_cases hk : k ≤ (i : ℤ)
  · rw [laurentShiftL2_apply_of_le k _ i hk]
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> first | rfl | omega
  · cases k with
    | ofNat n =>
      change ¬ (n : ℤ) ≤ (i : ℤ) at hk
      rw [laurentShiftL2, forwardShiftL2_pow_apply_of_lt n _ i (by omega)]
      have hne : (i : ℤ)-j ≠ (n : ℤ) := by omega
      change 0 = if (i : ℤ)-j = (n : ℤ) then 1 else 0
      rw [ite_eq_right hne]
    | negSucc n => omega

/-- A product of signed shifts differs from the combined shift only near zero. -/
theorem laurentShiftL2_mul_sub_apply_eq_zero (k l : ℤ) (u : H) (i : ℕ)
    (h : k.natAbs+l.natAbs ≤ i) :
    ((laurentShiftL2 k * laurentShiftL2 l - laurentShiftL2 (k+l)) : H →L[𝕜] H) u i = 0 := by
  have hk : k ≤ (i : ℤ) := by omega
  have hkl : k+l ≤ (i : ℤ) := by omega
  have hl : l ≤ (((i : ℤ)-k).toNat : ℤ) := by omega
  change laurentShiftL2 k (laurentShiftL2 l u) i - laurentShiftL2 (k+l) u i = 0
  rw [laurentShiftL2_apply_of_le k _ i hk, laurentShiftL2_apply_of_le l _ _ hl,
    laurentShiftL2_apply_of_le (k+l) _ i hkl]
  have he : ((((i : ℤ)-k).toNat : ℤ)-l).toNat = ((i : ℤ)-(k+l)).toNat := by omega
  rw [he, sub_self]

/-- Bounded operators whose outputs have a uniform finite coordinate cutoff. -/
def finiteCoordinateRange : Submodule 𝕜 (H →L[𝕜] H) where
  carrier := {A | ∃ N : ℕ, ∀ u i, N ≤ i → A u i = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro A B ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, ?_⟩
    intro u i hi
    change A u i+B u i = 0
    rw [hN u i (by omega), hM u i (by omega), add_zero]
  smul_mem' := by
    rintro a A ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro u i hi
    change a • A u i = 0
    rw [hN u i hi, smul_zero]

/-- Finite coordinate range means some initial projection fixes the operator. -/
theorem initialL2Projection_comp_eq_of_mem_finiteCoordinateRange
    {A : H →L[𝕜] H} (hA : A ∈ finiteCoordinateRange) :
    ∃ N, (initialL2Projection N).comp A = A := by
  obtain ⟨N, hN⟩ := hA
  refine ⟨N, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, initialL2Projection_apply, lp.coeFn_sum,
    lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single, Finset.mem_range]
  split_ifs with h
  · rfl
  · exact (hN u i (by omega)).symm

/-- Operators with finite coordinate range are compact. -/
theorem isCompactOperator_of_mem_finiteCoordinateRange
    {A : H →L[𝕜] H} (hA : A ∈ finiteCoordinateRange) : IsCompactOperator A := by
  obtain ⟨N, hN⟩ := initialL2Projection_comp_eq_of_mem_finiteCoordinateRange hA
  rw [← hN]
  exact (isCompactOperator_initialL2Projection N).comp_clm A

/-- Finite coordinate range is in particular finite-dimensional range. -/
theorem finiteDimensional_range_of_mem_finiteCoordinateRange
    {A : H →L[𝕜] H} (hA : A ∈ finiteCoordinateRange) :
    FiniteDimensional 𝕜 (LinearMap.range A.toLinearMap) := by
  classical
  obtain ⟨N, hN⟩ := initialL2Projection_comp_eq_of_mem_finiteCoordinateRange hA
  let s : Finset H := (Finset.range N).image (fun i ↦ lp.single 2 i (1 : 𝕜))
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span 𝕜 (s : Set H))
  rintro v ⟨u, rfl⟩
  have he : A u = initialL2Projection N (A u) :=
    (congrArg (fun T : H →L[𝕜] H ↦ T u) hN).symm
  change A u ∈ Submodule.span 𝕜 (s : Set H)
  rw [he, initialL2Projection_apply]
  apply Submodule.sum_mem
  intro i hi
  have hs : lp.single 2 i (1 : 𝕜) ∈ Submodule.span 𝕜 (s : Set H) :=
    Submodule.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  simpa only [← lp.single_smul, smul_eq_mul, mul_one] using
    (Submodule.smul_mem (Submodule.span 𝕜 (s : Set H)) (A u i) hs)

/-- Laurent-polynomial product defects have finite coordinate range. -/
theorem laurentToeplitz_mul_sub_mem_finiteCoordinateRange (p q : LaurentPolynomial 𝕜) :
    laurentToeplitz p * laurentToeplitz q - laurentToeplitz (p*q) ∈
      finiteCoordinateRange := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, zero_mul, sub_self]; exact Submodule.zero_mem _
  | add p r hp hr =>
    simpa only [map_add, add_mul, add_sub_add_comm] using Submodule.add_mem _ hp hr
  | single k a =>
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp only [map_zero, mul_zero, sub_self]; exact Submodule.zero_mem _
    | add q r hq hr =>
      simpa only [map_add, mul_add, add_sub_add_comm] using Submodule.add_mem _ hq hr
    | single l b =>
      rw [AddMonoidAlgebra.single_mul_single, laurentToeplitz_single,
        laurentToeplitz_single, laurentToeplitz_single]
      have he : (a • laurentShiftL2 k) * (b • laurentShiftL2 l) -
          (a*b) • laurentShiftL2 (k+l) =
          (a*b) • (laurentShiftL2 k * laurentShiftL2 l - laurentShiftL2 (k+l) : H →L[𝕜] H) := by
        apply ContinuousLinearMap.ext
        intro u
        simp only [sub_apply, mul_apply_eq_comp,
          smul_apply, map_smul, smul_smul, smul_sub, mul_comm]
      rw [he]
      apply Submodule.smul_mem
      exact ⟨k.natAbs+l.natAbs, laurentShiftL2_mul_sub_apply_eq_zero k l⟩

/-- Products of Laurent-polynomial Toeplitz operators agree modulo finite rank. -/
theorem finiteDimensional_range_laurentToeplitz_mul_sub (p q : LaurentPolynomial 𝕜) :
    FiniteDimensional 𝕜 (LinearMap.range
      (laurentToeplitz p * laurentToeplitz q - laurentToeplitz (p*q)).toLinearMap) :=
  finiteDimensional_range_of_mem_finiteCoordinateRange
    (laurentToeplitz_mul_sub_mem_finiteCoordinateRange p q)

/-- Products of Laurent-polynomial Toeplitz operators agree modulo compact operators. -/
theorem isCompactOperator_laurentToeplitz_mul_sub (p q : LaurentPolynomial 𝕜) :
    IsCompactOperator (fun u : H ↦
      (laurentToeplitz p * laurentToeplitz q - laurentToeplitz (p*q)) u) :=
  isCompactOperator_of_mem_finiteCoordinateRange
    (laurentToeplitz_mul_sub_mem_finiteCoordinateRange p q)

end lp
