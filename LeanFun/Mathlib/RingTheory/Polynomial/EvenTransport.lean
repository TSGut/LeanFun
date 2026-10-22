/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.CharZero.Infinite
public import LeanFun.Mathlib.RingTheory.Polynomial.Reflection
/-!
# Transport of even polynomials under an affine squared coordinate

The inverse substitution preserves even polynomial degrees and positive leading
coefficients for a positive parameter. This supplies the algebraic part of the
outer-measure deformation in Cartesian disk systems.
Reference: Dunkl–Xu, §2.6.1 (separated polynomial construction).
-/

@[expose] public section
namespace Polynomial

/-- Every polynomial with vanishing odd coefficients is a polynomial in `X²`. -/
theorem comp_sq_contract_of_even_coeff (p : ℝ[X])
    (hp : ∀ i, i % 2 ≠ 0 → p.coeff i = 0) :
    (p.contract 2).comp (X^2) = p := by
  rw [← expand_eq_comp_X_pow]
  ext i
  rw [coeff_expand (by norm_num : 0 < 2)]
  split_ifs with hi
  · rw [coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
    congr 1
    omega
  · exact (hp i (by simpa only [Nat.dvd_iff_mod_eq_zero] using hi)).symm

/-- Transport an even polynomial using the inverse affine squared coordinate. -/
noncomputable def evenDiskTransport (δ : {δ : ℝ // δ ≠ 0}) (p : ℝ[X]) : ℝ[X] :=
  (p.contract 2).comp (C (δ : ℝ)⁻¹ * (X^2 - C (1-(δ : ℝ))))

/-- The inverse substitution recovers an even polynomial on either branch. -/
theorem eval_evenDiskTransport_sq (δ : ℝ) (hδ : δ ≠ 0) (p : ℝ[X])
    (hp : ∀ i, i % 2 ≠ 0 → p.coeff i = 0) (x t : ℝ)
    (hx : x^2 = 1-δ+δ*t^2) :
    (evenDiskTransport ⟨δ,hδ⟩ p).eval x = p.eval t := by
  have he := congrArg (fun q : ℝ[X] => q.eval t) (comp_sq_contract_of_even_coeff p hp)
  simp only [eval_comp, eval_pow, eval_X] at he
  rw [evenDiskTransport, eval_comp]
  have ha : (C δ⁻¹ * (X^2-C (1-δ)) : ℝ[X]).eval x = t^2 := by
    simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X, hx]
    field_simp
    ring
  rw [ha, he]
/-- For a polynomial in `X²`, transport is ordinary polynomial composition. -/
theorem evenDiskTransport_comp_sq (δ : {δ : ℝ // δ ≠ 0}) (q : ℝ[X]) :
    evenDiskTransport δ (q.comp (X^2)) = q.comp (C (δ : ℝ)⁻¹ * (X^2-C (1-(δ : ℝ)))) := by
  unfold evenDiskTransport
  rw [← expand_eq_comp_X_pow, contract_expand 2 (by norm_num : (2 : ℕ) ≠ 0)]

/-- The transported polynomial is even. -/
theorem even_eval_evenDiskTransport (δ : {δ : ℝ // δ ≠ 0}) (p : ℝ[X]) :
    Function.Even (evenDiskTransport δ p).eval := by
  intro x
  simp [evenDiskTransport, eval_comp]

/-- A nonzero deformation parameter preserves the degree of a polynomial in `X²`. -/
theorem natDegree_evenDiskTransport_comp_sq (δ : ℝ) (hδ : δ ≠ 0) (q : ℝ[X]) :
    (evenDiskTransport ⟨δ,hδ⟩ (q.comp (X^2))).natDegree = (q.comp (X^2)).natDegree := by
  rw [evenDiskTransport_comp_sq, natDegree_comp, natDegree_comp]
  have hd : (C δ⁻¹ * (X^2-C (1-δ)) : ℝ[X]).natDegree = 2 := by
    rw [natDegree_C_mul (inv_ne_zero hδ), natDegree_sub_C, natDegree_X_pow]
  rw [hd, natDegree_X_pow]

/-- The leading coefficient acquires the inverse parameter to half the degree. -/
theorem leadingCoeff_evenDiskTransport_comp_sq (δ : ℝ) (hδ : δ ≠ 0) (q : ℝ[X]) :
    (evenDiskTransport ⟨δ,hδ⟩ (q.comp (X^2))).leadingCoeff =
      (q.comp (X^2)).leadingCoeff * δ⁻¹^q.natDegree := by
  rw [evenDiskTransport_comp_sq]
  have hd : (C δ⁻¹ * (X^2-C (1-δ)) : ℝ[X]).natDegree = 2 := by
    rw [natDegree_C_mul (inv_ne_zero hδ), natDegree_sub_C, natDegree_X_pow]
  rw [leadingCoeff_comp (by rw [hd]; norm_num),
    leadingCoeff_comp (by simp : (X^2 : ℝ[X]).natDegree ≠ 0), leadingCoeff_mul,
    leadingCoeff_C, leadingCoeff_sub_of_degree_lt (by
      exact (degree_C_le).trans_lt (by simp : (0 : WithBot ℕ) < (X^2 : ℝ[X]).degree))]
  simp


/-- Transport preserves the degree of every even polynomial. -/
theorem natDegree_evenDiskTransport (δ : ℝ) (hδ : δ ≠ 0) (p : ℝ[X])
    (hp : ∀ i, i % 2 ≠ 0 → p.coeff i = 0) :
    (evenDiskTransport ⟨δ,hδ⟩ p).natDegree = p.natDegree := by
  have he := natDegree_evenDiskTransport_comp_sq δ hδ (p.contract 2)
  rwa [comp_sq_contract_of_even_coeff p hp] at he

/-- A positive parameter preserves positivity of the leading coefficient. -/
theorem leadingCoeff_evenDiskTransport_pos (δ : ℝ) (hδ : 0 < δ) (p : ℝ[X])
    (hp : ∀ i, i % 2 ≠ 0 → p.coeff i = 0) (hl : 0 < p.leadingCoeff) :
    0 < (evenDiskTransport ⟨δ,hδ.ne'⟩ p).leadingCoeff := by
  have he := leadingCoeff_evenDiskTransport_comp_sq δ hδ.ne' (p.contract 2)
  rw [comp_sq_contract_of_even_coeff p hp] at he
  rw [he]
  exact mul_pos hl (pow_pos (inv_pos.mpr hδ) _)

/-- Every transported polynomial has vanishing odd coefficients. -/
theorem coeff_evenDiskTransport_eq_zero (δ : {δ : ℝ // δ ≠ 0}) (p : ℝ[X]) (i : ℕ) (hi : i % 2 ≠ 0) :
    (evenDiskTransport δ p).coeff i = 0 := by
  apply coeff_eq_zero_of_reflection 0 i _ (by simpa using hi)
  apply Polynomial.funext
  intro x
  simpa only [eval_comp, eval_neg, eval_X, pow_zero, C_1, one_mul] using
    even_eval_evenDiskTransport δ p x

/-- The transported polynomial is explicitly a polynomial in `X²`. -/
theorem evenDiskTransport_eq_comp_sq (δ : {δ : ℝ // δ ≠ 0}) (p : ℝ[X]) :
    evenDiskTransport δ p =
      ((p.contract 2).comp (C (δ : ℝ)⁻¹ * (X-C (1-(δ : ℝ))))).comp (X^2) := by
  rw [evenDiskTransport, comp_assoc]
  congr 1
  simp only [mul_comp, C_comp, sub_comp, X_comp]

/-- Transport by the reciprocal parameter is the inverse on even polynomials. -/
theorem evenDiskTransport_inv (δ : ℝ) (hδ : δ ≠ 0) (p : ℝ[X])
    (hp : ∀ i, i % 2 ≠ 0 → p.coeff i = 0) :
    evenDiskTransport ⟨δ⁻¹,inv_ne_zero hδ⟩ (evenDiskTransport ⟨δ,hδ⟩ p) = p := by
  rw [evenDiskTransport_eq_comp_sq ⟨δ,hδ⟩ p, evenDiskTransport_comp_sq, comp_assoc]
  have he : (C δ⁻¹ * (X-C (1-δ))).comp
      (C (δ⁻¹)⁻¹ * (X^2-C (1-δ⁻¹))) = (X^2 : ℝ[X]) := by
    simp only [mul_comp, C_comp, sub_comp, X_comp, inv_inv]
    have hc : C δ⁻¹ * C δ = (1 : ℝ[X]) := by rw [← C_mul, inv_mul_cancel₀ hδ, C_1]
    simp only [map_sub, map_one]
    linear_combination (X^2+C δ⁻¹)*hc
  rw [he, comp_sq_contract_of_even_coeff p hp]

end Polynomial
