/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Completeness

/-! # Parseval for the Chebyshev coefficients
The full constant term has squared norm pi; all other terms have pi/2.
Reference: DLMF 18.2(viii); ATAP, Chapter 3.
-/

public section
namespace Polynomial.Chebyshev
open MeasureTheory Real
open scoped InnerProductSpace

private theorem inner_hilbertBasisT_mul (f : Lp ℝ 2 classicalMeasureT) (n : ℕ) :
    ⟪f, hilbertBasisT n⟫_ℝ * ⟪hilbertBasisT n, f⟫_ℝ =
      (if n = 0 then π else π / 2) * (coefficient (n := n) ⟨f, coefficientInput_integrable_L2 f _⟩) ^ 2 := by
  have h := congrArg (fun v : Lp ℝ 2 classicalMeasureT ↦ ⟪v, v⟫_ℝ)
    (hilbertBasisT_repr_smul f n)
  have hb : ⟪hilbertBasisT n, hilbertBasisT n⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hilbertBasisT.orthonormal.norm_eq_one, one_pow]
  simp only [inner_smul_left, inner_smul_right, conj_trivial, hb,
    inner_polynomialToL2_T, ite_true, mul_one, HilbertBasis.repr_apply_apply] at h
  rw [real_inner_comm (hilbertBasisT n) f]
  nlinarith [h]

/-- Parseval as a convergent series, not merely an equality of total tsums. -/
theorem hasSum_coefficient_energy (f : Lp ℝ 2 classicalMeasureT) :
    HasSum (fun n ↦ (if n = 0 then π else π / 2) * (coefficient (n := n) ⟨f, coefficientInput_integrable_L2 f _⟩) ^ 2)
      (∫ x, f x ^ 2 ∂classicalMeasureT) := by
  have h := hilbertBasisT.hasSum_inner_mul_inner f f
  simp_rw [inner_hilbertBasisT_mul] at h
  simpa only [L2.inner_def, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using h

/-- Parseval in the full-constant Chebyshev convention. -/
theorem integral_sq_eq_sum_coefficient_sq (f : Lp ℝ 2 classicalMeasureT) :
    ∫ x, f x ^ 2 ∂classicalMeasureT =
      π * (coefficient (n := 0) ⟨f, coefficientInput_integrable_L2 f _⟩) ^ 2 + π / 2 * ∑' n : ℕ, (coefficient (n := (n + 1)) ⟨f, coefficientInput_integrable_L2 f _⟩) ^ 2 := by
  have h := (hasSum_coefficient_energy f).summable.sum_add_tsum_nat_add 1
  rw [(hasSum_coefficient_energy f).tsum_eq] at h
  simpa only [Finset.sum_range_one, ite_true, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ite_false, tsum_mul_left] using h.symm

end Polynomial.Chebyshev
