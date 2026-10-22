/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UniversalConnection
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# General Jacobi connection expansions

Reflection gives second-parameter conversion. Composing the two finite
conversions gives an explicit expansion for arbitrary source and target
parameters, with all denominators cleared. Reference: DLMF 18.18(iv).
-/

public section
namespace Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The second-parameter connection formula follows by reflection from
DLMF 18.18.14, with all denominators cleared. -/
theorem jacobiBetaConnectionScale_smul (α β δ : R) (n : ℕ) :
    jacobiAlphaConnectionScale β α n • jacobi α δ n =
      ∑ k : Fin (n + 1),
        ((-1 : R) ^ (n + k) * jacobiAlphaConnectionCleared β α δ n k) • jacobi α β k := by
  have h := congrArg (fun p : R[X] ↦ p.comp (-X)) (jacobiAlphaConnectionScale_smul β α δ n)
  simp only [smul_comp, sum_comp, jacobi_comp_neg_X, ← smul_eq_C_mul, smul_smul] at h
  have hh := congrArg (fun p : R[X] ↦ (-1 : R) ^ n • p) h
  rw [Finset.smul_sum] at hh
  simp only [smul_smul] at hh
  have he : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by rw [← mul_pow]; simp
  rw [show (-1 : R) ^ n * (jacobiAlphaConnectionScale β α n * (-1 : R) ^ n) =
    jacobiAlphaConnectionScale β α n by rw [mul_left_comm, he, mul_one]] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [pow_add]
  ring

/-- Composing the two explicit one-parameter conversions gives the general
Jacobi connection identity over every commutative rational algebra. All
parameters, including degenerate specializations, are allowed (DLMF 18.18(iv)). -/
theorem jacobi_generalConnection_cleared (α β γ δ : R) (n : ℕ) :
    (jacobiAlphaConnectionScale α δ n *
      ∏ i : Fin (n + 1), jacobiAlphaConnectionScale β α i) • jacobi γ δ n =
      ∑ i : Fin (n + 1), ∑ j : Fin ((i : ℕ) + 1),
        (jacobiAlphaConnectionCleared α δ γ n i *
          (∏ l ∈ Finset.univ.erase i, jacobiAlphaConnectionScale β α l) *
          ((-1 : R) ^ ((i : ℕ) + j) * jacobiAlphaConnectionCleared β α δ i j)) •
          jacobi α β j := by
  rw [mul_comm, ← smul_smul, jacobiAlphaConnectionScale_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hp := Finset.mul_prod_erase Finset.univ
    (fun l : Fin (n + 1) ↦ jacobiAlphaConnectionScale β α l) (Finset.mem_univ i)
  calc
    _ = (jacobiAlphaConnectionCleared α δ γ n i *
        ∏ l ∈ Finset.univ.erase i, jacobiAlphaConnectionScale β α l) •
        (jacobiAlphaConnectionScale β α i • jacobi α δ i) := by
      rw [smul_smul, smul_smul, ← hp]
      congr 1
      ring
    _ = _ := by
      rw [jacobiBetaConnectionScale_smul, Finset.smul_sum]
      simp only [smul_smul]

/-- Over a field, a nonzero common denominator gives the divided general
Jacobi connection expansion. Its coefficients are an explicit finite convolution
of the one-parameter coefficients (DLMF 18.18(iv)). -/
theorem jacobi_eq_sum_generalConnection {K : Type*} [Field K] [Algebra ℚ K]
    (α β γ δ : K) (n : ℕ)
    (hD : jacobiAlphaConnectionScale α δ n *
      (∏ i : Fin (n + 1), jacobiAlphaConnectionScale β α i) ≠ 0) :
    jacobi γ δ n =
      ∑ i : Fin (n + 1), ∑ j : Fin ((i : ℕ) + 1),
        ((jacobiAlphaConnectionCleared α δ γ n i *
          (∏ l ∈ Finset.univ.erase i, jacobiAlphaConnectionScale β α l) *
          ((-1 : K) ^ ((i : ℕ) + j) * jacobiAlphaConnectionCleared β α δ i j)) /
          (jacobiAlphaConnectionScale α δ n *
            ∏ l : Fin (n + 1), jacobiAlphaConnectionScale β α l)) • jacobi α β j := by
  have h := congrArg (fun p : K[X] ↦
      (jacobiAlphaConnectionScale α δ n *
        ∏ i : Fin (n + 1), jacobiAlphaConnectionScale β α i)⁻¹ • p)
    (jacobi_generalConnection_cleared α β γ δ n)
  simpa only [Finset.smul_sum, smul_smul, inv_mul_cancel₀ hD, one_smul,
    div_eq_mul_inv, mul_comm] using h

/-- The composed connection scale is positive when both intermediate and target
Jacobi families lie in the orthogonality range (DLMF 18.18(iv)). -/
theorem jacobi_generalConnection_scale_pos {α β δ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : -1 < δ) (n : ℕ) :
    0 < jacobiAlphaConnectionScale α δ n *
      ∏ i : Fin (n + 1), jacobiAlphaConnectionScale β α i := by
  apply mul_pos
  · exact Finset.prod_pos (fun i _ ↦ jacobiAlphaConnectionDenominator_pos hα hδ n i)
  · exact Finset.prod_pos (fun i _ ↦
      Finset.prod_pos (fun j _ ↦ jacobiAlphaConnectionDenominator_pos hβ hα i j))

end Polynomial
