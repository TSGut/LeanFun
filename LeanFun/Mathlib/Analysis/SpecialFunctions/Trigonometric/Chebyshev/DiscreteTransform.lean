/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.DiscreteOrthogonality
public import LeanFun.Mathlib.Algebra.Polynomial.Sequence
public import LeanFun.Mathlib.LinearAlgebra.Barycentric
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClassicalNodes

/-! # The exact DCT-I and Chebyshev interpolation
The normalization uses a full constant coefficient and also halves the highest
coefficient. No floating-point or rational-cosine assumption is made.
Reference: ATAP, Chapter 4; Olver–Townsend (2013), Section 2.
-/

@[expose] public section
namespace Polynomial.Chebyshev

/-- DCT-I coefficients on positive-order extrema, in the full-constant convention. -/
noncomputable def extremaCoefficient (N : {n : ℕ // 0 < n}) (f : ℝ → ℝ)
    (k : Fin (N.val + 1)) : ℝ :=
  (if k.val = 0 ∨ k.val = N.val then 1 else 2) / N.val *
    extremaSum N (fun j ↦ f (classicalNode N j) *
      (T ℝ k.val).eval (classicalNode N j))

/-- The finite cosine formula for a resolved coefficient (ATAP, Chapter 4). -/
theorem extremaCoefficient_eq_sum {N : ℕ} (hN : N ≠ 0) (f : ℝ → ℝ)
    (k : Fin (N + 1)) :
    extremaCoefficient ⟨N, Nat.pos_of_ne_zero hN⟩ f k =
      (if k.val = 0 ∨ k.val = N then 1 else 2) / N *
      extremaSum ⟨N, Nat.pos_of_ne_zero hN⟩
        (fun j ↦ f (node N j) * (T ℝ k.val).eval (node N j)) := rfl

/-- Classical positive-order DCT-I formula, in the full-constant convention. -/
theorem extremaCoefficient_positive (N : {n : ℕ // 0 < n}) (f : ℝ → ℝ)
    (k : Fin (N.val + 1)) :
    extremaCoefficient N f k = (if k.val = 0 ∨ k.val = N.val then 1 else 2) / N.val *
      extremaSum N (fun j ↦ f (classicalNode N j) *
        (T ℝ k.val).eval (classicalNode N j)) := rfl

/-- Additivity of the finite transform needs no regularity assumption. -/
theorem extremaCoefficient_add (N : {n : ℕ // 0 < n}) (f g : ℝ → ℝ)
    (k : Fin (N.val + 1)) :
    extremaCoefficient N (fun x ↦ f x + g x) k =
      extremaCoefficient N f k + extremaCoefficient N g k := by
  simp only [extremaCoefficient, add_mul, extremaSum_add, mul_add]

/-- Homogeneity of the finite transform. -/
theorem extremaCoefficient_mul (N : {n : ℕ // 0 < n}) (a : ℝ) (f : ℝ → ℝ)
    (k : Fin (N.val + 1)) :
    extremaCoefficient N (fun x ↦ a * f x) k = a * extremaCoefficient N f k := by
  simp only [extremaCoefficient, mul_assoc, extremaSum_mul]
  ring

/-- The DCT-I recovers each resolved Chebyshev mode exactly, including both endpoints. -/
theorem extremaCoefficient_eval_T {N j k : ℕ} (hN : N ≠ 0) (hj : j ≤ N) (hk : k ≤ N) :
    extremaCoefficient ⟨N, Nat.pos_of_ne_zero hN⟩ (fun x ↦ (T ℝ j).eval x)
      ⟨k, Nat.lt_succ_of_le hk⟩ = if j = k then 1 else 0 := by
  rw [extremaCoefficient_eq_sum hN]
  by_cases h : j = k
  · subst j
    rw [ite_eq_left rfl]
    simp only [← pow_two]
    rw [extremaSum_sq_eval_T hN hk]
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    split_ifs <;> field_simp
  · rw [extremaSum_mul_eval_T_eq_zero hj hk h, mul_zero, ite_eq_right h]

/-- The polynomial assembled from DCT-I coefficients. -/
noncomputable def dctInterpolant (N : ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  if h : N = 0 then Polynomial.C (f 1) else
    ∑ k : Fin (N + 1),
      Polynomial.C (extremaCoefficient ⟨N, Nat.pos_of_ne_zero h⟩ f k) * T ℝ k.val

/-- Resolved polynomial data are reconstructed exactly by the DCT-I. -/
theorem dctInterpolant_eval {N : ℕ} (hN : N ≠ 0) {p : ℝ[X]} (hp : p.degree ≤ N) :
    dctInterpolant N (fun x ↦ p.eval x) = p := by
  have hm : p ∈ Submodule.span ℝ (chebyshevTsequence ℝ '' Set.Iic N) := by
    rw [(chebyshevTsequence ℝ).span_degreeLE
      (fun i _ ↦ (chebyshevTsequence ℝ).isUnit_leadingCoeff i), mem_degreeLE]
    exact hp
  clear hp
  induction hm using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨j, hj, rfl⟩ := hp
    change j ≤ N at hj
    change dctInterpolant N (fun x ↦ (T ℝ j).eval x) = T ℝ j
    simp only [dctInterpolant, dite_eq_right hN]
    have he (k : Fin (N + 1)) :=
      extremaCoefficient_eval_T hN hj (Nat.le_of_lt_succ k.isLt)
    simp_rw [he]
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ Polynomial.C (if j = k then (1 : ℝ) else 0) * T ℝ k)]
    simp [show j < N + 1 by omega]
  | zero => simp [dctInterpolant, extremaCoefficient, extremaSum]
  | add p q _ _ hp hq =>
    simp only [eval_add, dctInterpolant, dite_eq_right hN, extremaCoefficient_add, map_add,
      add_mul, Finset.sum_add_distrib] at hp hq ⊢
    rw [hp, hq]
  | smul a p _ hp =>
    simp only [eval_smul, smul_eq_mul, extremaCoefficient_mul, dctInterpolant, dite_eq_right hN,
      map_mul, mul_assoc, ← Finset.mul_sum] at hp ⊢
    rw [hp]
    exact (smul_eq_C_mul a).symm


/-- The DCT-I reconstructs classical distinct-node interpolation. -/
theorem dctInterpolant_eq_lagrange (N : {n : ℕ // 0 < n}) (f : ℝ → ℝ) :
    dctInterpolant N.val f =
      Lagrange.classicalInterpolate (Finset.range (N.val + 1)) (classicalNode N)
        ⟨(strictAntiOn_classicalNode N).injOn⟩ (fun j ↦ f (classicalNode N j)) := by
  rcases N with ⟨N,hNp⟩
  have hN := Nat.ne_of_gt hNp
  change dctInterpolant N f = Lagrange.interpolate (Finset.range (N+1)) (node N)
    (fun j ↦ f (node N j))
  let p := Lagrange.interpolate (Finset.range (N + 1)) (node N) (fun j ↦ f (node N j))
  have hv := (strictAntiOn_node N).injOn
  have hp : p.degree ≤ N := by
    have h := Lagrange.degree_interpolate_lt (fun j ↦ f (node N j)) hv
    simp only [Finset.card_range] at h
    by_cases hz : p = 0
    · simp [hz]
    · exact degree_le_of_natDegree_le
        (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hz).2 h))
  have he (j : ℕ) (hj : j ≤ N) : p.eval (node N j) = f (node N j) :=
    Lagrange.eval_interpolate_at_node _ hv (Finset.mem_range.mpr (by omega))
  change dctInterpolant N f = p
  rw [← dctInterpolant_eval hN hp]
  simp only [dctInterpolant, dite_eq_right hN]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  simp only [extremaCoefficient_eq_sum hN]
  unfold extremaSum
  dsimp only
  rw [he N le_rfl, he 0 (Nat.zero_le N)]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j (by simpa using (Finset.mem_range.mp hj).le)]
/-- The inverse DCT-I takes exactly the supplied values at every extrema node. -/
theorem eval_dctInterpolant_node {N : ℕ} (hN : N ≠ 0) (f : ℝ → ℝ)
    {j : ℕ} (hj : j ≤ N) : (dctInterpolant N f).eval (node N j) = f (node N j) := by
  rw [dctInterpolant_eq_lagrange ⟨N,Nat.pos_of_ne_zero hN⟩]
  exact Lagrange.eval_classicalInterpolate
    (s := Finset.range (N+1)) (v := classicalNode ⟨N,Nat.pos_of_ne_zero hN⟩)
    _ _ ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le hj)⟩


/-- Order zero agrees with the constant singleton interpolant. -/
theorem dctInterpolant_zero (f : ℝ → ℝ) : dctInterpolant 0 f = Polynomial.C (f 1) := by
  simp [dctInterpolant]

end Polynomial.Chebyshev
