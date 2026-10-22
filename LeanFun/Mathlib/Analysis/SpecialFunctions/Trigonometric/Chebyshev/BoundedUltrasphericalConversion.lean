/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.BoundedCoefficientOperators
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Compact conversion between positive ultraspherical levels
The conversion from C^(k+1) to C^(k+2) factors into a two-diagonal bounded
operator and a vanishing diagonal. It agrees with polynomial basis conversion.
Reference: Olver--Townsend (2013), Section 4.1.
-/

@[expose] public noncomputable section
namespace Polynomial.Chebyshev
open Filter ContinuousLinearMap
open scoped Topology

/-- Diagonal coefficient (k+1)/(n+k+1) for positive-level conversion. -/
def positiveConversionDiagonal (k n : ℕ) : ℂ :=
  (((k : ℝ) + 1) / ((n : ℝ) + k + 1) : ℝ)

/-- Each conversion diagonal coefficient has norm at most one. -/
theorem norm_positiveConversionDiagonal_le (k n : ℕ) :
    ‖positiveConversionDiagonal k n‖ ≤ 1 := by
  rw [positiveConversionDiagonal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity : (0 : ℝ) < n + k + 1)).2
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The positive-level conversion diagonal tends to zero. -/
theorem tendsto_positiveConversionDiagonal (k : ℕ) :
    Tendsto (positiveConversionDiagonal k) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ ((n : ℝ) + k + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1
        (tendsto_atTop_add_const_right atTop (k : ℝ)
          (tendsto_natCast_atTop_atTop (R := ℝ))))
  change Tendsto (fun n : ℕ ↦ (((((k : ℝ) + 1) / ((n : ℝ) + k + 1)) : ℝ) : ℂ)) atTop (𝓝 0)
  simp only [div_eq_mul_inv]
  simpa only [Function.comp_def, mul_zero, Complex.ofReal_zero] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp (h.const_mul ((k : ℝ) + 1))

/-- The diagonal scaling in positive-level ultraspherical conversion. -/
def positiveConversionScaling (k : ℕ) :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  lp.coefficientDiagonal (positiveConversionDiagonal k) zero_le_one
    (norm_positiveConversionDiagonal_le k)

/-- Bounded conversion from C^(k+1) to C^(k+2) on raw square-summable coefficients. -/
def boundedPositiveConversion (k : ℕ) :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  (1 - lp.coefficientShiftLeft.comp lp.coefficientShiftLeft).comp
    (positiveConversionScaling k)

/-- Conversion has exactly its diagonal and second superdiagonal entries. -/
theorem boundedPositiveConversion_apply (k : ℕ)
    (x : lp (fun _ : ℕ ↦ ℂ) 2) (i : ℕ) :
    boundedPositiveConversion k x i =
      positiveConversionDiagonal k i * x i -
        positiveConversionDiagonal k (i + 2) * x (i + 2) := rfl

/-- Every positive-level conversion is compact on raw coefficient space. -/
theorem isCompactOperator_boundedPositiveConversion (k : ℕ) :
    IsCompactOperator (boundedPositiveConversion k) := by
  unfold boundedPositiveConversion positiveConversionScaling
  exact (lp.isCompactOperator_coefficientDiagonal (positiveConversionDiagonal k) zero_le_one
    (norm_positiveConversionDiagonal_le k) (tendsto_positiveConversionDiagonal k)).clm_comp
      (1 - lp.coefficientShiftLeft.comp lp.coefficientShiftLeft)

/-- The continuous conversion agrees with the canonical polynomial coordinates. -/
theorem boundedPositiveConversion_coefficientLp (k : ℕ) (p : ℝ[X]) :
    boundedPositiveConversion k ((ultrasphericalBasis (k + 1)).coefficientLp p) =
      (ultrasphericalBasis (k + 2)).coefficientLp p := by
  have hb (j : ℕ) : ultrasphericalBasis (k + 2) j = gegenbauer ((k : ℝ) + 1 + 1) j := by
    simp [show k + 2 = (k + 1) + 1 by omega]
  have h : ((boundedPositiveConversion k).restrictScalars ℝ).toLinearMap.comp
      (ultrasphericalBasis (k + 1)).coefficientLp =
      (ultrasphericalBasis (k + 2)).coefficientLp := by
    apply (ultrasphericalBasis (k + 1)).ext
    intro j
    change boundedPositiveConversion k
      ((ultrasphericalBasis (k + 1)).coefficientLp (ultrasphericalBasis (k + 1) j)) = _
    rw [Module.Basis.coefficientLp_basis]
    ext i
    rw [Module.Basis.coefficientLp_apply, ultrasphericalBasis_succ_apply]
    change boundedPositiveConversion k (lp.single 2 j (1 : ℂ)) i =
      (((ultrasphericalBasis (k + 2)).toMatrix (gegenbauer ((k : ℝ) + 1)) i j : ℝ) : ℂ)
    rw [boundedPositiveConversion_apply]
    have hn (n : ℕ) : ((n : ℂ) + k + 1) ≠ 0 := by
      exact_mod_cast (show ((n : ℝ) + k + 1) ≠ 0 by positivity)
    have hcol :
        positiveConversionDiagonal k i * lp.single (E := fun _ : ℕ ↦ ℂ) 2 j 1 i -
        positiveConversionDiagonal k (i + 2) * lp.single (E := fun _ : ℕ ↦ ℂ) 2 j 1 (i + 2) =
        (if i = j then positiveConversionDiagonal k j else 0) -
          (if i + 2 = j then positiveConversionDiagonal k j else 0) := by
      simp only [lp.single_apply, Pi.single_apply]
      split_ifs <;> simp_all
    rw [hcol]
    rcases j with _ | (_ | j)
    · rw [gegenbauer_conversion_matrix_zero _ _ hb]
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      simp [positiveConversionDiagonal, hk, apply_ite Complex.ofReal]
    · have he := gegenbauer_conversion_matrix_one ((k : ℝ) + 1)
        (ultrasphericalBasis (k + 2)) hb i
      have hc := congrArg (fun x : ℝ ↦ (x : ℂ)) he
      have hd : ((k : ℂ) + 1 + 1) ≠ 0 := by
        exact_mod_cast (show ((k : ℝ) + 1 + 1) ≠ 0 by positivity)
      apply (mul_left_cancel₀ hd)
      split_ifs at hc ⊢ <;> try omega
      all_goals push_cast at hc
      all_goals try simp only [positiveConversionDiagonal]
      all_goals push_cast
      all_goals ring_nf at hc hd ⊢
      all_goals field_simp [hd]
      all_goals first | linear_combination -hc | linear_combination -(2 + (k : ℂ)) * hc
    · have he := gegenbauer_conversion_matrix_add_two ((k : ℝ) + 1)
        (ultrasphericalBasis (k + 2)) hb j i
      have hc := congrArg (fun x : ℝ ↦ (x : ℂ)) he
      have hd : ((j : ℂ) + ((k : ℂ) + 1) + 2) ≠ 0 := by
        exact_mod_cast (show ((j : ℝ) + ((k : ℝ) + 1) + 2) ≠ 0 by positivity)
      apply (mul_left_cancel₀ hd)
      split_ifs at hc ⊢ <;> try omega
      all_goals push_cast at hc
      all_goals try simp only [positiveConversionDiagonal]
      all_goals push_cast
      all_goals ring_nf at hc hd ⊢
      all_goals field_simp [hd]
      all_goals first | linear_combination -hc | linear_combination -(3 + (j : ℂ) + k) * hc

  exact congrArg (fun L : ℝ[X] →ₗ[ℝ] lp (fun _ : ℕ ↦ ℂ) 2 ↦ L p) h

end Polynomial.Chebyshev
