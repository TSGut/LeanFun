/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ExtremaNodal
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Interpolation

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Barycentric interpolation at Chebyshev extrema

Alternating weights have half magnitude at both endpoints. Evaluation at a node
uses its prescribed value; away from all nodes the barycentric denominator is nonzero.
Reference: ATAP, Chapter 5.
-/

@[expose] public section
namespace Polynomial.Chebyshev

/-- Alternating barycentric weights, with half-weight endpoints (ATAP, Chapter 5). -/
noncomputable def extremaBarycentricWeight (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) : ℝ :=
  (-1) ^ j.val / extremaEndpointFactor N j

/-- The endpoint factor is positive (ATAP, Chapter 5). -/
theorem extremaEndpointFactor_pos (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) : 0 < extremaEndpointFactor N j := by
  unfold extremaEndpointFactor
  split_ifs <;> norm_num


/-- The common scaling factor in the barycentric weights is nonzero (ATAP, Chapter 5). -/
theorem extremaBarycentricScale_ne_zero {N : ℕ} (hN : N ≠ 0) :
    (extremaNodal ⟨N, by omega⟩).leadingCoeff / (N : ℝ) ^ 2 ≠ 0 :=
  div_ne_zero (leadingCoeff_ne_zero.mpr (extremaNodal_ne_zero hN))
    (pow_ne_zero _ (by exact_mod_cast hN))





/-- Real nodes give separated complex nodes whenever the real product is classical. -/
theorem complex_basisInput {s : Finset ℕ} {v : ℕ → ℝ} {j : ℕ}
    (d : Lagrange.BasisInput s v j) :
    Lagrange.BasisInput s (fun i ↦ (v i : ℂ)) j :=
  ⟨fun i hi h ↦ d.separated i hi (Complex.ofReal_injective h)⟩

/-- Classical product weights at positive-order extrema (ATAP, Chapter 5). -/
theorem nodalWeight_extrema (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) :
    Lagrange.classicalNodalWeight (Finset.range (N.val + 1)) (classicalNode N) j
      (Lagrange.BasisInput.of_injOn (strictAntiOn_classicalNode N).injOn
        (Finset.mem_range.mpr j.isLt)) =
      (extremaNodal N).leadingCoeff / (N.val : ℝ) ^ 2 *
        extremaBarycentricWeight N j := by
  rcases N with ⟨N,hNp⟩
  have hN := Nat.ne_of_gt hNp
  rcases j with ⟨j,hjp⟩
  change j < N+1 at hjp
  have hj := Nat.le_of_lt_succ hjp
  change Lagrange.nodalWeight (Finset.range (N + 1)) (node N) j =
      (extremaNodal ⟨N, by omega⟩).leadingCoeff / (N : ℝ) ^ 2 * extremaBarycentricWeight ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩
  have hmem : j ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  let d := (derivative (Lagrange.nodal (Finset.range (N + 1)) (node N))).eval (node N j)
  have hd : d ≠ 0 := by
    dsimp only [d]
    rw [Lagrange.eval_nodal_derivative_eval_node_eq hmem]
    apply Lagrange.eval_nodal_not_at_node
    intro i hi hji
    exact (Finset.mem_erase.mp hi).1
      ((strictAntiOn_classicalNode ⟨N,Nat.pos_of_ne_zero hN⟩).injOn
        (Finset.mem_erase.mp hi).2 hmem hji.symm)
  have he : (extremaNodal ⟨N, by omega⟩).leadingCoeff * d =
      extremaEndpointFactor ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩ * (N : ℝ) ^ 2 * (-1) ^ j := by
    have h := congrArg (fun p : ℝ[X] ↦ (derivative p).eval (node N j))
      (extremaNodal_eq_leadingCoeff_mul_nodal hN)
    simpa only [eval_derivative_extremaNodal_node hN hj, derivative_C_mul,
      eval_mul, eval_C] using h.symm
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hmem]
  change d⁻¹ = _
  apply (mul_right_cancel₀ hd)
  rw [inv_mul_cancel₀ hd]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hE := (extremaEndpointFactor_pos ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩).ne'
  unfold extremaBarycentricWeight
  field_simp [hNr, hE]
  have hs : (-1 : ℝ) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; simp
  linear_combination -(-1 : ℝ) ^ j * he -
    extremaEndpointFactor ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩ * (N : ℝ) ^ 2 * hs

/-- Complex classical product weights (ATAP, Chapter 5). -/
theorem nodalWeight_complex_extrema (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1)) :
    Lagrange.classicalNodalWeight (Finset.range (N.val + 1))
      (fun i ↦ (classicalNode N i : ℂ)) j
      (complex_basisInput (Lagrange.BasisInput.of_injOn
        (strictAntiOn_classicalNode N).injOn (Finset.mem_range.mpr j.isLt))) =
      (((extremaNodal N).leadingCoeff / (N.val : ℝ) ^ 2 : ℝ) : ℂ) *
        (extremaBarycentricWeight N j : ℂ) := by
  rcases N with ⟨N,hNp⟩
  have hN := Nat.ne_of_gt hNp
  rcases j with ⟨j,hjp⟩
  change j < N+1 at hjp
  have hj := Nat.le_of_lt_succ hjp
  change Lagrange.nodalWeight (Finset.range (N + 1)) (fun i ↦ (node N i : ℂ)) j =
      (((extremaNodal ⟨N, by omega⟩).leadingCoeff / (N : ℝ) ^ 2 : ℝ) : ℂ) *
        (extremaBarycentricWeight ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩ : ℂ)
  have h := congrArg Complex.ofReal (nodalWeight_extrema ⟨N,hNp⟩ ⟨j,hjp⟩)
  simpa [Lagrange.classicalNodalWeight, classicalNode, Lagrange.nodalWeight] using h

/-- Nonvanishing on the classical off-grid domain (ATAP, Chapter 5). -/
theorem extremaBarycentric_denominator_ne_zero (N : {n : ℕ // 0 < n})
    (z : {z : ℂ // ∀ j ≤ N.val, z ≠ (classicalNode N j : ℂ)}) :
    (∑ j : Fin (N.val + 1), (extremaBarycentricWeight N j : ℂ) /
      (z.val - (classicalNode N j : ℂ))) ≠ 0 := by
  rcases N with ⟨N,hNp⟩
  have hN := Nat.ne_of_gt hNp
  rcases z with ⟨z,hz⟩
  change ∀ j ≤ N, z ≠ (node N j : ℂ) at hz
  have hv : Set.InjOn (fun j ↦ (node N j : ℂ)) (Finset.range (N+1)) :=
    Complex.ofReal_injective.comp_injOn (strictAntiOn_classicalNode ⟨N,hNp⟩).injOn
  change (∑ j : Fin (N + 1), (extremaBarycentricWeight ⟨N, by omega⟩ j : ℂ) /
      (z - (node N j : ℂ))) ≠ 0
  have h := Lagrange.sum_nodalWeight_mul_inv_sub_ne_zero hv
    (fun j hj ↦ hz j (by simpa using hj)) (Finset.nonempty_range_iff.mpr (by omega))
  have he : (∑ j ∈ Finset.range (N + 1),
      Lagrange.nodalWeight (Finset.range (N + 1)) (fun i ↦ (node N i : ℂ)) j *
        (z - (node N j : ℂ))⁻¹) =
      (((extremaNodal ⟨N, by omega⟩).leadingCoeff / (N : ℝ) ^ 2 : ℝ) : ℂ) *
        ∑ j : Fin (N + 1), (extremaBarycentricWeight ⟨N, by omega⟩ j : ℂ) /
          (z - (node N j : ℂ)) := by
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have hw := nodalWeight_complex_extrema ⟨N,hNp⟩ j
    change Lagrange.nodalWeight (Finset.range (N+1)) (fun i ↦ (node N i : ℂ)) j = _ at hw
    rw [hw]
    simp only [div_eq_mul_inv, mul_assoc]
  rw [he] at h
  exact (mul_ne_zero_iff.mp h).2

/-- Barycentric evaluation on its classical domain (ATAP, Chapter 5). -/
theorem eval_extremaInterpolant_barycentric (N : {n : ℕ // 0 < n}) (f : ℝ → ℂ)
    (z : {z : ℂ // ∀ j ≤ N.val, z ≠ (classicalNode N j : ℂ)}) :
    (extremaInterpolant N.val f).eval z.val =
      (∑ j : Fin (N.val + 1), (extremaBarycentricWeight N j : ℂ) /
        (z.val - (classicalNode N j : ℂ)) * f (classicalNode N j)) /
      (∑ j : Fin (N.val + 1), (extremaBarycentricWeight N j : ℂ) /
        (z.val - (classicalNode N j : ℂ))) := by
  rcases N with ⟨N,hNp⟩
  have hN := Nat.ne_of_gt hNp
  rcases z with ⟨z,hz⟩
  change ∀ j ≤ N, z ≠ (node N j : ℂ) at hz
  have hv : Set.InjOn (fun j ↦ (node N j : ℂ)) (Finset.range (N+1)) :=
    Complex.ofReal_injective.comp_injOn (strictAntiOn_classicalNode ⟨N,hNp⟩).injOn
  change (extremaInterpolant N f).eval z =
      (∑ j : Fin (N + 1), (extremaBarycentricWeight ⟨N, by omega⟩ j : ℂ) /
        (z - (node N j : ℂ)) * f (node N j)) /
      (∑ j : Fin (N + 1), (extremaBarycentricWeight ⟨N, by omega⟩ j : ℂ) /
        (z - (node N j : ℂ)))
  rw [extremaInterpolant_positive ⟨N,Nat.pos_of_ne_zero hN⟩]
  change (Lagrange.interpolate (Finset.range (N+1)) (fun j ↦ (node N j : ℂ))
    (fun j ↦ f (node N j))).eval z = _
  rw [Lagrange.eval_interpolate_not_at_node'
    _ hv (Finset.nonempty_range_iff.mpr (by omega))
      (fun j hj ↦ hz j (by simpa using hj))]
  have hsum (r : ℕ → ℂ) :
      (∑ j ∈ Finset.range (N + 1),
        Lagrange.nodalWeight (Finset.range (N + 1)) (fun i ↦ (node N i : ℂ)) j *
          (z - (node N j : ℂ))⁻¹ * r j) =
      (((extremaNodal ⟨N, by omega⟩).leadingCoeff / (N : ℝ) ^ 2 : ℝ) : ℂ) *
        ∑ j : Fin (N + 1), (extremaBarycentricWeight ⟨N, by omega⟩ j : ℂ) /
          (z - (node N j : ℂ)) * r j := by
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have hw := nodalWeight_complex_extrema ⟨N,hNp⟩ j
    change Lagrange.nodalWeight (Finset.range (N+1)) (fun i ↦ (node N i : ℂ)) j = _ at hw
    rw [hw]
    simp only [div_eq_mul_inv, mul_assoc]
  rw [hsum]
  have hone := hsum (fun _ ↦ 1)
  simp only [mul_one] at hone
  rw [hone, mul_div_mul_left]
  exact_mod_cast extremaBarycentricScale_ne_zero hN

/-- Classical real cardinal evaluation off its own node (ATAP, Chapter 5). -/
theorem eval_extremaBasis (N : {n : ℕ // 0 < n}) (j : Fin (N.val + 1))
    (x : {x : ℝ // x ≠ classicalNode N j}) :
    (Lagrange.classicalBasis (Finset.range (N.val + 1)) (classicalNode N) j
      (Lagrange.BasisInput.of_injOn (strictAntiOn_classicalNode N).injOn
        (Finset.mem_range.mpr j.isLt))).eval x.val =
      (extremaNodal N).eval x.val * (-1) ^ (j : ℕ) /
        ((N.val : ℝ) ^ 2 * extremaEndpointFactor N j * (x.val - classicalNode N j)) := by
  rcases N with ⟨N,hNp⟩
  have hN := Nat.ne_of_gt hNp
  rcases j with ⟨j,hjp⟩
  change j < N+1 at hjp
  have hj := Nat.le_of_lt_succ hjp
  rcases x with ⟨x,hx⟩
  change x ≠ node N j at hx
  change (Lagrange.basis (Finset.range (N + 1)) (node N) j).eval x =
      (extremaNodal ⟨N, by omega⟩).eval x * (-1) ^ j /
        ((N : ℝ) ^ 2 * extremaEndpointFactor ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩ * (x - node N j))
  have hlc := leadingCoeff_ne_zero.mpr (extremaNodal_ne_zero hN)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have he := congrArg (fun p : ℝ[X] ↦ p.eval x)
    (extremaNodal_eq_leadingCoeff_mul_nodal hN)
  simp only [eval_mul, eval_C] at he
  have hnval : (Lagrange.nodal (Finset.range (N + 1)) (node N)).eval x =
      (extremaNodal ⟨N, by omega⟩).eval x / (extremaNodal ⟨N, by omega⟩).leadingCoeff := by
    apply (eq_div_iff hlc).mpr
    simpa [mul_comm] using he.symm
  have hw := nodalWeight_extrema ⟨N,hNp⟩ ⟨j,hjp⟩
  change Lagrange.nodalWeight (Finset.range (N+1)) (node N) j = _ at hw
  rw [Lagrange.eval_basis_not_at_node (Finset.mem_range.mpr (by omega)) hx,
    hw, hnval, extremaBarycentricWeight]
  field_simp [hlc, hn, (extremaEndpointFactor_pos ⟨N, by omega⟩ ⟨j, by change j < N + 1; omega⟩).ne', sub_ne_zero.mpr hx]

end Polynomial.Chebyshev

/-- Complex evaluation of a real classical normalized nodal product.
The normalization index need not belong to the interpolation set (DLMF §3.3(i)). -/
theorem Lagrange.eval_classicalBasis_complex (s : Finset ℕ) (v : ℕ → ℝ) (j : ℕ)
    (d : Lagrange.BasisInput s v j) (x : ℝ) :
    (Lagrange.classicalBasis s (fun i ↦ (v i : ℂ)) j
      (Polynomial.Chebyshev.complex_basisInput d)).eval (x : ℂ) =
      (((Lagrange.classicalBasis s v j d).eval x : ℝ) : ℂ) := by
  simp [Lagrange.classicalBasis, Lagrange.basis, Lagrange.basisDivisor,
    Polynomial.eval_prod]
