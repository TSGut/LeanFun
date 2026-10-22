/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraToeplitzAlgebra

/-! # A sufficient coefficient condition for first-kind operator approximation

Absolute monomial coefficients, weighted by powers of the two ordered factor
norms, control the preconditioned operator norm. This is a sufficient condition,
not a sharp regularity classification. Reference: Gutleb's thesis, §2.7,
Lemma 2.5 (operator-norm approximation hypothesis).
-/

@[expose] public noncomputable section
open Polynomial Filter
open scoped Topology
namespace MvPolynomial

/-- An explicit finite coefficient majorant for ordered first-kind quantization. -/
def volterraKernelMajorant (K : MvPolynomial (Fin 2) ℝ) : ℝ :=
  ∑ d ∈ K.support, ‖K.coeff d‖ *
    (‖reflectedJacobiOneZeroL2‖^(d 0)*‖shiftedJacobiOneZeroL2‖^(d 1))

private theorem operator_pow_bound
    (A : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2) (n : ℕ) :
    ‖A^n‖ ≤ ‖A‖^n := by
  cases n with
  | zero =>
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n => exact norm_pow_le' A (Nat.succ_pos n)

/-- The coefficient majorant bounds the preconditioned operator norm. -/
theorem norm_volterraPreconditionedL2_le_majorant (K : MvPolynomial (Fin 2) ℝ) :
    ‖volterraPreconditionedL2 K‖ ≤ volterraKernelMajorant K := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _hd
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_mul_le _ _).trans
    (mul_le_mul (operator_pow_bound _ _) (operator_pow_bound _ _) (norm_nonneg _) (by positivity))

/-- Vanishing weighted coefficient error is sufficient for operator-norm consistency. -/
theorem tendsto_volterraPreconditionedL2_of_majorant
    (L : ℕ → MvPolynomial (Fin 2) ℝ) (K : MvPolynomial (Fin 2) ℝ)
    (h : Tendsto (fun N ↦ volterraKernelMajorant (L N-K)) atTop (𝓝 0)) :
    Tendsto (fun N ↦ volterraPreconditionedL2 (L N)) atTop
      (𝓝 (volterraPreconditionedL2 K)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) h
  have he : volterraPreconditionedL2 (L N-K) =
      volterraPreconditionedL2 (L N)-volterraPreconditionedL2 K :=
    volterraPreconditionedLinear.map_sub (L N) K
  rw [← he]
  exact norm_volterraPreconditionedL2_le_majorant _

/-- Summable coefficient majorants give an absolutely convergent ordered operator series. -/
theorem summable_volterraPreconditionedL2_of_majorant
    (p : ℕ → MvPolynomial (Fin 2) ℝ)
    (h : Summable (fun n ↦ volterraKernelMajorant (p n))) :
    Summable (fun n ↦ volterraPreconditionedL2 (p n)) :=
  h.of_norm_bounded (fun n ↦ norm_volterraPreconditionedL2_le_majorant (p n))

/-- Polynomial partial sums converge in preconditioned operator norm under the majorant test.
Identification with an integral operator is a separate obligation. -/
theorem tendsto_volterraPreconditionedL2_sum_of_majorant
    (p : ℕ → MvPolynomial (Fin 2) ℝ)
    (h : Summable (fun n ↦ volterraKernelMajorant (p n))) :
    Tendsto (fun N ↦ volterraPreconditionedL2 (∑ n ∈ Finset.range N, p n)) atTop
      (𝓝 (∑' n, volterraPreconditionedL2 (p n))) := by
  have he (N : ℕ) : volterraPreconditionedL2 (∑ n ∈ Finset.range N, p n) =
      ∑ n ∈ Finset.range N, volterraPreconditionedL2 (p n) :=
    map_sum volterraPreconditionedLinear p (Finset.range N)
  simp_rw [he]
  exact (summable_volterraPreconditionedL2_of_majorant p h).hasSum.tendsto_sum_nat

end MvPolynomial
