/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.LinearAlgebra.Barycentric
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ClassicalNodes
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Aliasing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ComplexSeries

/-!
# Chebyshev-extrema interpolation

Lagrange interpolation, aliasing, and the error bound of ATAP, Theorem 8.2.
-/

public section

namespace Polynomial.Chebyshev

open Real Set Complex


/-- Interpolation at positive-order extrema, with the separate singleton at `1`
for order zero (ATAP Chapters 4 and 8). -/
@[expose] noncomputable def extremaInterpolant (N : ℕ) (f : ℝ → ℂ) : ℂ[X] :=
  if h : N = 0 then Polynomial.C (f 1) else
    Lagrange.classicalInterpolate (Finset.range (N + 1))
      (fun j ↦ (classicalNode ⟨N, Nat.pos_of_ne_zero h⟩ j : ℂ))
      ⟨Complex.ofReal_injective.comp_injOn (strictAntiOn_classicalNode ⟨N,Nat.pos_of_ne_zero h⟩).injOn⟩ (fun j ↦ f (classicalNode ⟨N, Nat.pos_of_ne_zero h⟩ j))


/-- The order-zero classical extension is interpolation at the singleton `1`. -/
theorem extremaInterpolant_zero (f : ℝ → ℂ) : extremaInterpolant 0 f = Polynomial.C (f 1) := by
  simp [extremaInterpolant]

/-- Positive-order extrema interpolation is classical interpolation at cosine nodes. -/
theorem extremaInterpolant_positive (N : {n : ℕ // 0 < n}) (f : ℝ → ℂ) :
    extremaInterpolant N.val f = Lagrange.classicalInterpolate (Finset.range (N.val + 1))
      (fun j ↦ (classicalNode N j : ℂ)) ⟨Complex.ofReal_injective.comp_injOn (strictAntiOn_classicalNode N).injOn⟩
      (fun j ↦ f (classicalNode N j)) := by
  simp only [extremaInterpolant, dite_eq_right (Nat.ne_of_gt N.property)]


/-- Interpolation at a node on the classical positive-order grid. -/
theorem eval_extremaInterpolant_classicalNode (N : {n : ℕ // 0 < n})
    (f : ℝ → ℂ) (j : Fin (N.val + 1)) :
    (extremaInterpolant N.val f).eval (classicalNode N j : ℂ) = f (classicalNode N j) := by
  rw [extremaInterpolant_positive N]
  exact Lagrange.eval_classicalInterpolate
    (s := Finset.range (N.val+1)) (v := fun k ↦ (classicalNode N k : ℂ))
    _ _ ⟨j.val, Finset.mem_range.mpr j.isLt⟩

/-- The extrema interpolant has degree at most `N`. -/
theorem degree_extremaInterpolant_lt (N : ℕ) (f : ℝ → ℂ) :
    (extremaInterpolant N f).degree < (N + 1 : ℕ) := by
  by_cases h : N = 0
  · subst N
    rw [extremaInterpolant_zero]
    simpa using (degree_C_lt (a := f 1))
  · rw [extremaInterpolant_positive ⟨N,Nat.pos_of_ne_zero h⟩]
    simpa only [Lagrange.classicalInterpolate,Finset.card_range] using
      Lagrange.degree_interpolate_lt (v := fun j ↦ (classicalNode ⟨N,Nat.pos_of_ne_zero h⟩ j : ℂ))
        (fun j ↦ f (classicalNode ⟨N,Nat.pos_of_ne_zero h⟩ j)) (Complex.ofReal_injective.comp_injOn (strictAntiOn_classicalNode ⟨N,Nat.pos_of_ne_zero h⟩).injOn)

/-- Interpolation folds a Chebyshev frequency into `[0,N]` (ATAP, Chapter 4). -/
theorem extremaInterpolant_T {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    extremaInterpolant N (fun t : ℝ ↦ (((T ℝ k).eval t : ℝ) : ℂ)) = T ℂ (aliasIndex N k) := by
  symm
  rw [extremaInterpolant_positive ⟨N,Nat.pos_of_ne_zero hN⟩]
  apply Lagrange.eq_interpolate_of_eval_eq _
    (Complex.ofReal_injective.comp_injOn (strictAntiOn_classicalNode ⟨N,Nat.pos_of_ne_zero hN⟩).injOn)
  · simp only [degree_T, Int.natAbs_natCast, Finset.card_range]
    exact_mod_cast (Nat.lt_succ_of_le (aliasIndex_le hN k))
  · intro j hj
    dsimp only [Function.comp_def]
    rw [← complex_ofReal_eval_T]
    exact congrArg Complex.ofReal
      (eval_T_node_aliasIndex ⟨N,Nat.pos_of_ne_zero hN⟩ k j).symm

/-- Interpolating a single Chebyshev polynomial has norm at most one on the interval. -/
theorem norm_eval_extremaInterpolant_T_le_one {N : ℕ} (hN : N ≠ 0) (k : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    ‖(extremaInterpolant N (fun t : ℝ ↦ (((T ℝ k).eval t : ℝ) : ℂ))).eval (x : ℂ)‖ ≤ 1 := by
  rw [extremaInterpolant_T hN, ← complex_ofReal_eval_T, Complex.norm_real, Real.norm_eq_abs]
  exact abs_eval_T_real_le_one _ (abs_le.mpr hx)

/-- Classical cardinal polynomial on the finite extrema grid (ATAP Chapter 4).
For the singleton grid it is the constant one. -/
@[expose] noncomputable def extremaCardinal (N : ℕ) (j : Fin (N + 1)) : ℂ[X] :=
  if h : N = 0 then 1 else
    Lagrange.classicalBasis (Finset.range (N + 1))
      (fun i ↦ (classicalNode ⟨N, Nat.pos_of_ne_zero h⟩ i : ℂ)) j
      (Lagrange.BasisInput.of_injOn (Complex.ofReal_injective.comp_injOn (strictAntiOn_classicalNode ⟨N,Nat.pos_of_ne_zero h⟩).injOn) (Finset.mem_range.mpr j.isLt))


/-- Singleton cardinal polynomial. -/
theorem extremaCardinal_zero (j : Fin 1) : extremaCardinal 0 j = 1 := by
  simp [extremaCardinal]

/-- Positive-order cardinal polynomials are the classical Lagrange products. -/
theorem extremaCardinal_positive (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) :
    extremaCardinal N.val j = Lagrange.classicalBasis (Finset.range (N.val + 1))
      (fun i ↦ (classicalNode N i : ℂ)) j
      (Lagrange.BasisInput.of_injOn (Complex.ofReal_injective.comp_injOn (strictAntiOn_classicalNode N).injOn) (Finset.mem_range.mpr j.isLt)) := by
  simp [extremaCardinal, Nat.ne_of_gt N.property]

/-- Cardinal values on the entire finite grid. -/
theorem eval_extremaCardinal (N : ℕ) (i j : Fin (N + 1)) :
    (extremaCardinal N i).eval (extremaGridNode N j : ℂ) = if i = j then 1 else 0 := by
  by_cases hN : N = 0
  · subst N
    have hij : i = j := Fin.ext (by omega)
    simp [extremaCardinal_zero, hij]
  · rw [extremaCardinal_positive ⟨N,Nat.pos_of_ne_zero hN⟩,
      extremaGridNode_positive ⟨N,Nat.pos_of_ne_zero hN⟩]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      exact Lagrange.eval_classicalBasis_self (Finset.range (N+1))
        (fun k ↦ (classicalNode ⟨N,Nat.pos_of_ne_zero hN⟩ k : ℂ)) i.val _
    · rw [ite_eq_right hij]
      exact Lagrange.eval_classicalBasis_of_ne
        (v := fun k ↦ (classicalNode ⟨N,Nat.pos_of_ne_zero hN⟩ k : ℂ)) _ (fun h ↦ hij (Fin.ext h))
        (Finset.mem_range.mpr j.isLt)


/-- Evaluation as a finite sum of classical cardinal polynomials. -/
theorem eval_extremaInterpolant (N : ℕ) (f : ℝ → ℂ) (z : ℂ) :
    (extremaInterpolant N f).eval z = ∑ j : Fin (N + 1),
      f (extremaGridNode N j) * (extremaCardinal N j).eval z := by
  by_cases hN : N = 0
  · subst N
    simp [extremaInterpolant_zero, extremaCardinal_zero, extremaGridNode_zero]
  · rw [extremaInterpolant_positive ⟨N,Nat.pos_of_ne_zero hN⟩]
    simp only [extremaGridNode_positive ⟨N,Nat.pos_of_ne_zero hN⟩,
      extremaCardinal_positive ⟨N,Nat.pos_of_ne_zero hN⟩,
      Lagrange.classicalInterpolate, Lagrange.classicalBasis,
      Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
    exact (Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
      f (classicalNode ⟨N,Nat.pos_of_ne_zero hN⟩ j) *
        (Lagrange.basis (Finset.range (N+1))
          (fun k ↦ (classicalNode ⟨N,Nat.pos_of_ne_zero hN⟩ k : ℂ)) j).eval z) (N+1)).symm

/-- Interpolation commutes with ordinary partial-sum limits at its finitely many
nodes; absolute convergence is not required (ATAP, Chapters 4 and 8). -/
theorem tendsto_sum_eval_extremaInterpolant {N : ℕ} {a : ℕ → ℂ} {f : ℝ → ℂ}
    (hs : ∀ j : Fin (N + 1), Filter.Tendsto
      (fun m : ℕ ↦ ∑ k ∈ Finset.range m,
        a k * (((T ℝ k).eval (extremaGridNode N j) : ℝ) : ℂ))
      Filter.atTop (nhds (f (extremaGridNode N j)))) (z : ℂ) :
    Filter.Tendsto
      (fun m : ℕ ↦ ∑ k ∈ Finset.range m, a k *
        (extremaInterpolant N (fun t : ℝ ↦ (((T ℝ k).eval t : ℝ) : ℂ))).eval z)
      Filter.atTop (nhds ((extremaInterpolant N f).eval z)) := by
  simp_rw [eval_extremaInterpolant, Finset.mul_sum, ← mul_assoc]
  simp_rw [Finset.sum_comm (s := Finset.range _), ← Finset.sum_mul]
  exact tendsto_finsetSum _ fun j _ ↦ (hs j).mul_const _

/-- Interpolation commutes with an unconditionally convergent series at each node. -/
theorem hasSum_eval_extremaInterpolant {N : ℕ} {a : ℕ → ℂ} {f : ℝ → ℂ}
    (hs : ∀ j : Fin (N + 1), HasSum (fun k : ℕ ↦ a k * (((T ℝ k).eval (extremaGridNode N j) : ℝ) : ℂ))
      (f (extremaGridNode N j))) (z : ℂ) :
    HasSum (fun k : ℕ ↦ a k *
      (extremaInterpolant N (fun t : ℝ ↦ (((T ℝ k).eval t : ℝ) : ℂ))).eval z)
      ((extremaInterpolant N f).eval z) := by
  simp_rw [eval_extremaInterpolant, Finset.mul_sum, ← mul_assoc]
  exact hasSum_sum fun j hj ↦ (hs j).mul_right _

/-- Aliasing bounds interpolation error by twice the absolute coefficient tail
(ATAP, Chapter 4). -/
theorem norm_sub_extremaInterpolant_le_tsum_tail {N : ℕ} (hN : N ≠ 0)
    {a : ℕ → ℂ} {f : ℝ → ℂ} (ha : Summable (fun k ↦ ‖a k‖))
    (hf : ∀ x ∈ Icc (-1) 1,
      HasSum (fun k : ℕ ↦ a k * (((T ℝ k).eval x : ℝ) : ℂ)) (f x))
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    ‖f x - (extremaInterpolant N f).eval (x : ℂ)‖ ≤
      2 * ∑' k, ‖a (k + (N + 1))‖ := by
  let d (k : ℕ) : ℂ := a k * (((T ℝ k).eval x : ℝ) : ℂ) - a k *
    (extremaInterpolant N (fun t : ℝ ↦ (((T ℝ k).eval t : ℝ) : ℂ))).eval (x : ℂ)
  have hd : HasSum d (f x - (extremaInterpolant N f).eval (x : ℂ)) :=
    (hf x hx).sub (hasSum_eval_extremaInterpolant (fun j ↦ hf _ (extremaGridNode_mem_Icc N j)) (x : ℂ))
  have hz (k : ℕ) (hk : k ≤ N) : d k = 0 := by
    dsimp [d]
    rw [extremaInterpolant_T hN, aliasIndex_eq_self hN hk, ← complex_ofReal_eval_T,
      sub_self]
  have hb (k : ℕ) : ‖d k‖ ≤ 2 * ‖a k‖ := by
    dsimp [d]
    apply (norm_sub_le _ _).trans
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ht := abs_eval_T_real_le_one (k : ℤ) (abs_le.mpr hx)
    have hi := norm_eval_extremaInterpolant_T_le_one hN k hx
    nlinarith [norm_nonneg (a k)]
  have ht := ((summable_nat_add_iff (N + 1)).2 ha).mul_left 2
  have hn : Summable (fun k ↦ ‖d (k + (N + 1))‖) :=
    ht.of_norm_bounded (fun k ↦ by simpa only [norm_norm] using hb (k + (N + 1)))
  have he := hd.summable.sum_add_tsum_nat_add (N + 1)
  rw [hd.tsum_eq, Finset.sum_eq_zero (fun k hk ↦ hz k (by simpa using hk)), zero_add] at he
  rw [← he, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun k ↦ hb _) ht)

/-- A geometric coefficient majorant controls extrema interpolation error
(ATAP, Theorem 8.2). -/
theorem norm_sub_extremaInterpolant_le_geometric {a : ℕ → ℂ} {f : ℝ → ℂ}
    {C q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ n, ‖a n‖ ≤ C * q ^ n) {N : ℕ} (hN : N ≠ 0)
    (hf : ∀ t ∈ Icc (-1) 1,
      HasSum (fun n : ℕ ↦ a n * (((T ℝ n).eval t : ℝ) : ℂ)) (f t))
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    ‖f x - (extremaInterpolant N f).eval (x : ℂ)‖ ≤
      2 * (C * q ^ (N + 1) / (1 - q)) := by
  have hg := (summable_geometric_of_lt_one hq hq1).mul_left C
  have hs : Summable (fun n ↦ ‖a n‖) :=
    hg.of_norm_bounded (fun n ↦ by simpa only [norm_norm] using ha n)
  exact (norm_sub_extremaInterpolant_le_tsum_tail hN hs hf hx).trans
    (mul_le_mul_of_nonneg_left
      (tsum_tail_le_geometric hq hq1 (fun n ↦ norm_nonneg (a n)) ha (N + 1))
      (by norm_num))

/-- The analytic Chebyshev-extrema interpolation estimate on the whole closed
interval, with analyticity only in the open ellipse (ATAP, Theorem 8.2). -/
theorem norm_sub_extremaInterpolant_le_of_analytic {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ⟨ρ, hρ⟩))
    (hb : ∀ z ∈ bernsteinEllipse ⟨ρ, hρ⟩, ‖f z‖ ≤ M)
    {N : ℕ} (hN : N ≠ 0) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    ‖f x - (extremaInterpolant N (fun t : ℝ ↦ f t)).eval (x : ℂ)‖ ≤
      4 * M / (ρ ^ N * (ρ - 1)) := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hb x (ofReal_mem_bernsteinEllipse hρ hx))
  have hq : ρ⁻¹ < 1 := (inv_lt_one₀ hρ0).2 hρ
  have hc : ContinuousOn (fun t : ℝ ↦ f t) (Icc (-1) 1) :=
    hf.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun t ht ↦ ofReal_mem_bernsteinEllipse hρ ht)
  have hcoeff (n : ℕ) : ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun t : ℝ ↦ f t) (continuousOn_real_of_analytic hρ hf) n))‖ ≤ (2 * M) * (ρ⁻¹) ^ n := by
    apply (norm_complexCoefficient_le_of_analytic hρ hf hb n).trans
    rw [inv_pow, div_eq_mul_inv]
    gcongr
    split_ifs <;> norm_num
  have hg := (summable_geometric_of_lt_one (inv_nonneg.mpr hρ0.le) hq).mul_left (2 * M)
  have hs : Summable (fun n ↦ ‖(complexCoefficient (ComplexCoefficientInput.ofContinuousOn (fun t : ℝ ↦ f t) (continuousOn_real_of_analytic hρ hf) n))‖) :=
    hg.of_norm_bounded (fun n ↦ by simpa only [norm_norm] using hcoeff n)
  apply (norm_sub_extremaInterpolant_le_geometric (inv_nonneg.mpr hρ0.le) hq hcoeff hN
    (fun t ht ↦ hasSum_complexCoefficient_mul_eval_T hc hs ht) hx).trans_eq
  rw [inv_pow, pow_succ]
  field_simp
  ring

end Polynomial.Chebyshev
