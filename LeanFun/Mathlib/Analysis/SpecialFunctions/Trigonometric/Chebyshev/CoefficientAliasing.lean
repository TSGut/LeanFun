/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

import Mathlib.Topology.Algebra.Polynomial

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.DiscreteTransform
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Coefficients

/-! # Aliasing of coefficients
The DCT coefficients agree with the integral coefficients of the interpolant.
All source coefficients with the same folded frequency contribute to one output.
Reference: ATAP, Theorem 4.2.
-/

public section

namespace Polynomial.Chebyshev

/-- The discrete transform depends only on its nodal data. -/
theorem extremaCoefficient_congr {N : {n : ℕ // 0 < n}} {f g : ℝ → ℝ}
    (h : ∀ j : Fin (N.val + 1), f (extremaGridNode N.val j) = g (extremaGridNode N.val j))
    (k : Fin (N.val + 1)) :
    extremaCoefficient N f k = extremaCoefficient N g k := by
  rcases N with ⟨N, hNp⟩
  have hN := Nat.ne_of_gt hNp
  have h (j : ℕ) (hj : j ≤ N) : f (node N j) = g (node N j) := by
    simpa only [extremaGridNode_positive ⟨N,Nat.pos_of_ne_zero hN⟩, classicalNode]
      using h ⟨j,Nat.lt_succ_of_le hj⟩
  simp only [extremaCoefficient_eq_sum hN]
  unfold extremaSum
  dsimp only
  rw [h N le_rfl, h 0 (Nat.zero_le N)]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj).le]

/-- An arbitrary frequency contributes exactly to its folded DCT coefficient. -/
theorem extremaCoefficient_eval_T_alias {N k : ℕ} (hN : N ≠ 0) (hk : k ≤ N) (m : ℕ) :
    extremaCoefficient ⟨N, Nat.pos_of_ne_zero hN⟩ (fun x ↦ (T ℝ m).eval x)
      ⟨k, Nat.lt_succ_of_le hk⟩ =
      if aliasIndex N m = k then 1 else 0 := by
  rw [extremaCoefficient_congr (g := fun x ↦ (T ℝ (aliasIndex N m)).eval x)
    (fun j ↦ by simpa only [extremaGridNode_positive ⟨N,Nat.pos_of_ne_zero hN⟩] using
      eval_T_node_aliasIndex ⟨N,Nat.pos_of_ne_zero hN⟩ m j)]
  exact extremaCoefficient_eval_T hN (aliasIndex_le hN m) hk

/-- Finite sums commute with the discrete coefficient transform. -/
theorem extremaCoefficient_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (N : {n : ℕ // 0 < n}) (k : Fin (N.val + 1)) :
    extremaCoefficient N (fun x ↦ ∑ i ∈ s, f i x) k =
      ∑ i ∈ s, extremaCoefficient N (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [extremaCoefficient, extremaSum]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, extremaCoefficient_add, ih]

/-- Coefficient-level aliasing of a finite Chebyshev series (ATAP, Theorem 4.2). -/
theorem extremaCoefficient_sum_eval_T {N k : ℕ} (hN : N ≠ 0) (hk : k ≤ N)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    extremaCoefficient ⟨N, Nat.pos_of_ne_zero hN⟩
      (fun x ↦ ∑ m ∈ s, a m * (T ℝ m).eval x) ⟨k, Nat.lt_succ_of_le hk⟩ =
      ∑ m ∈ s, if aliasIndex N m = k then a m else 0 := by
  rw [extremaCoefficient_sum]
  simp only [extremaCoefficient_mul, extremaCoefficient_eval_T_alias hN hk,
    mul_ite, mul_one, mul_zero]

/-- The DCT normalization is exactly the project's weighted-integral coefficient
normalization on the interpolating polynomial, with zero coefficients above `N`. -/
theorem coefficient_dctInterpolant (N : ℕ) (f : ℝ → ℝ) (k : ℕ) :
    (coefficient (n := k) ⟨(fun x ↦ (dctInterpolant N f).eval x), by first | assumption | apply integrable_classicalMeasureT; fun_prop⟩) =
      if hN : N = 0 then (if k = 0 then f 1 else 0)
      else if hk : k ≤ N then
        extremaCoefficient ⟨N, Nat.pos_of_ne_zero hN⟩ f ⟨k, Nat.lt_succ_of_le hk⟩ else 0 := by
  by_cases hN : N = 0
  · subst N
    simpa only [dctInterpolant_zero, eval_C, dite_true, coefficient,
      CoefficientInput.ofContinuousOn_val] using coefficient_const (f 1) k
  simp only [dite_eq_right hN, dctInterpolant, eval_finsetSum, eval_mul, eval_C]
  simp only [coefficient, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ ↦ integrable_classicalMeasureT (by fun_prop)), Finset.mul_sum]
  simp only [mul_assoc, MeasureTheory.integral_const_mul]
  have hc (i : Fin (N + 1)) :
      (if k = 0 then 1 else 2) / Real.pi *
        (extremaCoefficient ⟨N, Nat.pos_of_ne_zero hN⟩ f i *
          ∫ x, (T ℝ i.val).eval x * (T ℝ k).eval x ∂classicalMeasureT) =
        extremaCoefficient ⟨N, Nat.pos_of_ne_zero hN⟩ f i *
          (if i.val = k then 1 else 0) := by
    rw [← coefficient_eval_T i.val k]
    simp only [coefficient, CoefficientInput.ofContinuousOn, CoefficientInput.ofL1]
    ring
  simp_rw [hc]
  by_cases hk : k ≤ N
  · rw [dite_eq_left hk, Finset.sum_eq_single (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N + 1))]
    · simp
    · intro b _ hb
      simp [show b.val ≠ k from fun h ↦ hb (Fin.ext h)]
    · simp
  · rw [dite_eq_right hk]
    apply Finset.sum_eq_zero
    intro b _
    simp [show b.val ≠ k by have := b.isLt; omega]

/-- A series summable at each sampled node may be transformed termwise,
since the transform is a finite linear combination of point evaluations.
Convergence here is `HasSum`, over finite subsets of indices. -/
theorem hasSum_extremaCoefficient {N : {n : ℕ // 0 < n}}
    {u : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hf : ∀ j : Fin (N.val + 1), HasSum (fun m ↦ u m (extremaGridNode N.val j))
      (f (extremaGridNode N.val j))) (k : Fin (N.val + 1)) :
    HasSum (fun m ↦ extremaCoefficient N (u m) k) (extremaCoefficient N f k) := by
  rcases N with ⟨N, hNp⟩
  have hN := Nat.ne_of_gt hNp
  have hf (j : ℕ) (hj : j ≤ N) : HasSum (fun m ↦ u m (node N j)) (f (node N j)) := by
    simpa only [extremaGridNode_positive ⟨N,Nat.pos_of_ne_zero hN⟩, classicalNode]
      using hf ⟨j,Nat.lt_succ_of_le hj⟩
  simp only [extremaCoefficient_eq_sum hN]
  have hs := hasSum_sum (s := Finset.range N) (fun j hj ↦
    (hf j (Finset.mem_range.mp hj).le).mul_right ((T ℝ k.val).eval (node N j)))
  have ht := (((hf N le_rfl).mul_right ((T ℝ k.val).eval (node N N))).sub
    ((hf 0 (Nat.zero_le N)).mul_right ((T ℝ k.val).eval (node N 0)))).div_const 2
  exact (hs.add ht).mul_left ((if k.val = 0 ∨ k.val = N then (1 : ℝ) else 2) / N)

/-- Coefficient aliasing for summable Chebyshev data, grouped by the exact
folding index. The nodal hypotheses use `HasSum` (unconditional convergence);
absolute summability of the source coefficients suffices (ATAP, Theorem 4.2). -/
theorem hasSum_alias_coefficients {N k : ℕ} (hN : N ≠ 0) (hk : k ≤ N)
    {a : ℕ → ℝ} {f : ℝ → ℝ}
    (hf : ∀ j : Fin (N + 1), HasSum (fun m ↦ a m * (T ℝ m).eval (extremaGridNode N j))
      (f (extremaGridNode N j))) :
    HasSum (fun m ↦ if aliasIndex N m = k then a m else 0) (extremaCoefficient ⟨N, Nat.pos_of_ne_zero hN⟩ f ⟨k, Nat.lt_succ_of_le hk⟩) := by
  have h := hasSum_extremaCoefficient (u := fun m x ↦ a m * (T ℝ m).eval x) (N := ⟨N, Nat.pos_of_ne_zero hN⟩) hf ⟨k, Nat.lt_succ_of_le hk⟩
  simpa only [extremaCoefficient_mul, extremaCoefficient_eval_T_alias hN hk,
    mul_ite, mul_one, mul_zero] using h

end Polynomial.Chebyshev
