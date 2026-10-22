/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2Preconditioner
public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.RealSymbol
public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.LaurentAsymptotic

/-! # The common Laurent symbol of the Jacobi Volterra factors

Both J and D⁻¹(I-J)D have symbol (2+z+z⁻¹)/4 modulo compact operators.
Reference: Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
namespace Polynomial

/-- The Laurent symbol of shifted Jacobi multiplication. -/
def shiftedJacobiLaurentSymbol : LaurentPolynomial ℝ :=
  AddMonoidAlgebra.single 0 (1/2) + AddMonoidAlgebra.single 1 (1/4) +
    AddMonoidAlgebra.single (-1) (1/4)

/-- Laurent quantization gives exactly the constant Jacobi tridiagonal part. -/
theorem laurentToeplitz_shiftedJacobiLaurentSymbol :
    lp.laurentToeplitz shiftedJacobiLaurentSymbol = shiftedJacobiToeplitzPart := by
  simp only [shiftedJacobiLaurentSymbol, map_add, lp.laurentToeplitz_single,
    lp.laurentShiftL2, pow_zero, pow_one, shiftedJacobiToeplitzPart, smul_add]
  abel

/-- Raw multiplication has the claimed Laurent symbol modulo a compact operator. -/
theorem isCompactOperator_shiftedJacobiOneZeroL2_sub_symbol :
    IsCompactOperator (shiftedJacobiOneZeroL2-lp.laurentToeplitz shiftedJacobiLaurentSymbol) := by
  rw [laurentToeplitz_shiftedJacobiLaurentSymbol, shiftedJacobiOneZeroL2, add_sub_cancel_left]
  exact isCompactOperator_shiftedJacobiOneZeroCorrection

/-- The reflected preconditioner has the same Laurent symbol modulo a compact operator. -/
theorem isCompactOperator_reflectedJacobiOneZeroL2_sub_symbol :
    IsCompactOperator (reflectedJacobiOneZeroL2-lp.laurentToeplitz shiftedJacobiLaurentSymbol) := by
  rw [laurentToeplitz_shiftedJacobiLaurentSymbol, reflectedJacobiOneZeroL2, add_sub_cancel_left]
  exact isCompactOperator_reflectedJacobiOneZeroCorrection

/-- Every ordered monomial in the two Jacobi factors has the diagonal power symbol. -/
theorem isCompactOperator_reflectedJacobi_pow_mul_sub_symbol (r s : ℕ) :
    IsCompactOperator (reflectedJacobiOneZeroL2^r*shiftedJacobiOneZeroL2^s-
      lp.laurentToeplitz (shiftedJacobiLaurentSymbol^(r+s))) := by
  rw [pow_add]
  exact lp.isCompactOperator_mul_sub_laurentToeplitz _ _ _ _
    (lp.isCompactOperator_pow_sub_laurentToeplitz _ _
      isCompactOperator_reflectedJacobiOneZeroL2_sub_symbol r)
    (lp.isCompactOperator_pow_sub_laurentToeplitz _ _
      isCompactOperator_shiftedJacobiOneZeroL2_sub_symbol s)

/-- The circle symbol is real and equals (1 + Re z)/2. -/
theorem shiftedJacobiLaurentSymbol_circle {T : {T : ℝ // T ≠ 0}} (x : AddCircle (T : ℝ)) :
    AddCircle.laurentSymbol (T := T)
      (AddMonoidAlgebra.mapRingHom ℤ Complex.ofRealHom shiftedJacobiLaurentSymbol) x =
      (((1+(fourier 1 x).re)/2 : ℝ) : ℂ) := by
  simp only [shiftedJacobiLaurentSymbol, map_add, AddMonoidAlgebra.mapRingHom_single,
    AddCircle.laurentSymbol_single, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    smul_eq_mul, fourier_zero, fourier_neg]
  apply Complex.ext <;> norm_num
  all_goals ring

/-- The common symbol takes values in the real unit interval. -/
theorem shiftedJacobiLaurentSymbol_circle_mem_Icc {T : {T : ℝ // T ≠ 0}} (x : AddCircle (T : ℝ)) :
    (1+(fourier 1 x).re)/2 ∈ Set.Icc (0 : ℝ) 1 := by
  have hnorm : ‖fourier 1 x‖ = 1 := Circle.norm_coe _
  have hr := Complex.abs_re_le_norm (fourier 1 x)
  rw [hnorm, abs_le] at hr
  constructor <;> linarith [hr.1, hr.2]

end Polynomial
