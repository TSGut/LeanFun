/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.Normed.Lp.DegreeWeightedOperators
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.BoundedUltrasphericalConversion
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.BoundedUltrasphericalMultiplication

/-! Ultraspherical operations on weighted coefficient spaces, OT §4.1. -/
@[expose] public noncomputable section

open Polynomial
namespace Module.Basis
/-- Finite polynomial coordinates in a degree-weighted sequence space. -/
def degreeWeightedCoefficient (b : Basis ℕ ℝ ℝ[X]) (s : ℕ) (p : ℝ[X]) : lp.DegreeWeightedL2 s :=
  ⟨fun i ↦ (b.repr p i : ℂ), by
    apply Memℓp.of_exponent_ge (p := 2) (q := 0) _ (by norm_num)
    apply memℓp_zero_iff.mpr
    apply (b.repr p).support.finite_toSet.subset
    intro i hi
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    exact fun hz ↦ hi (by simp [hz])⟩

/-- Weighted coordinates include into the usual polynomial coefficient sequence. -/
theorem degreeWeightedCoefficient_inclusion (b : Basis ℕ ℝ ℝ[X]) (s : ℕ) (p : ℝ[X]) :
    lp.degreeWeightedInclusion s (b.degreeWeightedCoefficient s p) = b.coefficientLp p := by
  ext i
  rw [lp.degreeWeightedInclusion_apply]
  rfl
/-- Polynomial coordinates preserve addition. -/
theorem degreeWeightedCoefficient_add (b : Basis ℕ ℝ ℝ[X]) (s : ℕ) (p q : ℝ[X]) :
    b.degreeWeightedCoefficient s (p + q) =
      b.degreeWeightedCoefficient s p + b.degreeWeightedCoefficient s q := by
  apply Subtype.ext
  funext i
  change ((b.repr (p + q) i : ℝ) : ℂ) = (b.repr p i : ℂ) + (b.repr q i : ℂ)
  simp

/-- Polynomial coordinates preserve real scalar multiplication. -/
theorem degreeWeightedCoefficient_smul (b : Basis ℕ ℝ ℝ[X]) (s : ℕ) (a : ℝ) (p : ℝ[X]) :
    b.degreeWeightedCoefficient s (a • p) = (a : ℂ) • b.degreeWeightedCoefficient s p := by
  apply Subtype.ext
  funext i
  change ((b.repr (a • p) i : ℝ) : ℂ) = (a : ℂ) * (b.repr p i : ℂ)
  simp
end Module.Basis

namespace Polynomial.Chebyshev
open ContinuousLinearMap

/-- The bounded T-to-U conversion on weighted coefficients. -/
def weightedChebyshevConversion (s : ℕ) : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  (1 / 2 : ℂ) • (1 - (lp.degreeWeightedShiftLeft s).comp (lp.degreeWeightedShiftLeft s)) +
    (1 / 2 : ℂ) • lp.degreeWeightedProjection s 1

/-- Weighted T-to-U conversion agrees with the ordinary coefficient operator. -/
theorem weightedChebyshevConversion_inclusion (s : ℕ) (x : lp.DegreeWeightedL2 s) :
    lp.degreeWeightedInclusion s (weightedChebyshevConversion s x) =
      boundedConversion (lp.degreeWeightedInclusion s x) := by
  ext i
  rw [lp.degreeWeightedInclusion_apply]
  change (1 / 2 : ℂ) * (x.1 i -
    (lp.degreeWeightedShiftLeft s (lp.degreeWeightedShiftLeft s x)).1 i) +
    (1 / 2 : ℂ) * (lp.degreeWeightedProjection s 1 x).1 i = _
  rw [lp.degreeWeightedShiftLeft_apply, lp.degreeWeightedShiftLeft_apply,
    lp.degreeWeightedProjection_apply]
  cases i with
  | zero => simp only [Nat.zero_lt_one, ite_true, boundedConversion_zero,
      lp.degreeWeightedInclusion_apply]; ring
  | succ i =>
    rw [ite_eq_right (by omega), boundedConversion_succ]
    simp only [lp.degreeWeightedInclusion_apply, Nat.add_assoc]
    ring

/-- Weighted T-to-U conversion agrees with polynomial basis conversion. -/
theorem weightedChebyshevConversion_coefficient (s : ℕ) (p : ℝ[X]) :
    weightedChebyshevConversion s (chebyshevBasis.degreeWeightedCoefficient s p) =
      (ultrasphericalBasis 1).degreeWeightedCoefficient s p := by
  apply lp.degreeWeightedInclusion_injective s
  rw [weightedChebyshevConversion_inclusion, Module.Basis.degreeWeightedCoefficient_inclusion,
    Module.Basis.degreeWeightedCoefficient_inclusion, boundedConversion_coefficientLp]

/-- Multiplication by x on weighted full-constant Chebyshev coefficients. -/
def weightedChebyshevMulX (s : ℕ) : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  (1 / 2 : ℂ) • ((lp.degreeWeightedShiftRight s).comp (1 + lp.degreeWeightedProjection s 1) +
    lp.degreeWeightedShiftLeft s)

/-- Weighted multiplication by x agrees with the ordinary coefficient operator. -/
theorem weightedChebyshevMulX_inclusion (s : ℕ) (x : lp.DegreeWeightedL2 s) :
    lp.degreeWeightedInclusion s (weightedChebyshevMulX s x) =
      boundedMulX (lp.degreeWeightedInclusion s x) := by
  ext i
  rw [lp.degreeWeightedInclusion_apply, boundedMulX_apply]
  change (1 / 2 : ℂ) * ((lp.degreeWeightedShiftRight s ((1 + lp.degreeWeightedProjection s 1) x)).1 i +
    (lp.degreeWeightedShiftLeft s x).1 i) = _
  rw [lp.degreeWeightedShiftLeft_apply]
  cases i with
  | zero =>
    simp only [lp.degreeWeightedShiftRight_zero, lp.coefficientShiftRight_zero,
      lp.degreeWeightedInclusion_apply, zero_add, Nat.zero_ne_one, ite_false, add_zero]
    ring
  | succ i =>
    rw [lp.degreeWeightedShiftRight_succ, lp.coefficientShiftRight_succ]
    change (1 / 2 : ℂ) * (x.1 i + (lp.degreeWeightedProjection s 1 x).1 i + x.1 (i + 1 + 1)) = _
    rw [lp.degreeWeightedProjection_apply]
    simp only [lp.degreeWeightedInclusion_apply]
    by_cases hi : i = 0
    · subst i
      norm_num
      ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      ring

/-- Weighted Chebyshev multiplication agrees with multiplication of polynomials. -/
theorem weightedChebyshevMulX_coefficient (s : ℕ) (p : ℝ[X]) :
    weightedChebyshevMulX s (chebyshevBasis.degreeWeightedCoefficient s p) =
      chebyshevBasis.degreeWeightedCoefficient s (X * p) := by
  apply lp.degreeWeightedInclusion_injective s
  rw [weightedChebyshevMulX_inclusion, Module.Basis.degreeWeightedCoefficient_inclusion,
    Module.Basis.degreeWeightedCoefficient_inclusion, boundedMulX_coefficientLp]

/-- One positive ultraspherical conversion step on weighted coefficients. -/
def weightedPositiveConversion (s k : ℕ) : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  (1 - (lp.degreeWeightedShiftLeft s).comp (lp.degreeWeightedShiftLeft s)).comp
    (lp.degreeWeightedDiagonal s (positiveConversionDiagonal k) zero_le_one
      (norm_positiveConversionDiagonal_le k))

/-- The two-diagonal coordinate formula for weighted conversion. -/
theorem weightedPositiveConversion_apply (s k : ℕ) (x : lp.DegreeWeightedL2 s) (i : ℕ) :
    (weightedPositiveConversion s k x).1 i =
      positiveConversionDiagonal k i * x.1 i -
        positiveConversionDiagonal k (i + 2) * x.1 (i + 2) := by
  change (lp.degreeWeightedDiagonal s _ _ _ x).1 i -
    (lp.degreeWeightedShiftLeft s (lp.degreeWeightedShiftLeft s
      (lp.degreeWeightedDiagonal s _ _ _ x))).1 i = _
  simp only [lp.degreeWeightedShiftLeft_apply, lp.degreeWeightedDiagonal_apply]

/-- Positive-level conversion is compact in every degree-weighted norm. -/
theorem isCompactOperator_weightedPositiveConversion (s k : ℕ) :
    IsCompactOperator (weightedPositiveConversion s k) := by
  unfold weightedPositiveConversion
  exact (lp.isCompactOperator_degreeWeightedDiagonal s (positiveConversionDiagonal k)
    zero_le_one (norm_positiveConversionDiagonal_le k) (tendsto_positiveConversionDiagonal k)).clm_comp
    (1 - (lp.degreeWeightedShiftLeft s).comp (lp.degreeWeightedShiftLeft s))

/-- Weighted conversion agrees with the ordinary coefficient operator. -/
theorem weightedPositiveConversion_inclusion (s k : ℕ) (x : lp.DegreeWeightedL2 s) :
    lp.degreeWeightedInclusion s (weightedPositiveConversion s k x) =
      boundedPositiveConversion k (lp.degreeWeightedInclusion s x) := by
  ext i
  simp only [lp.degreeWeightedInclusion_apply, weightedPositiveConversion_apply,
    boundedPositiveConversion_apply]

/-- Weighted conversion agrees with polynomial basis conversion. -/
theorem weightedPositiveConversion_coefficient (s k : ℕ) (p : ℝ[X]) :
    weightedPositiveConversion s k ((ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s p) =
      (ultrasphericalBasis (k + 2)).degreeWeightedCoefficient s p := by
  apply lp.degreeWeightedInclusion_injective s
  rw [weightedPositiveConversion_inclusion, Module.Basis.degreeWeightedCoefficient_inclusion,
    Module.Basis.degreeWeightedCoefficient_inclusion, boundedPositiveConversion_coefficientLp]

/-- Multiplication by x in a positive ultraspherical basis on weighted coefficients. -/
def weightedPositiveMulX (s k : ℕ) : lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  (lp.degreeWeightedShiftRight s).comp (lp.degreeWeightedDiagonal s (positiveMulXUp k)
    zero_le_one (norm_positiveMulXUp_le k)) +
  (lp.degreeWeightedShiftLeft s).comp (lp.degreeWeightedDiagonal s (positiveMulXDown k)
    zero_le_one (norm_positiveMulXDown_le k))

/-- Weighted ultraspherical multiplication agrees with its ordinary coefficient operator. -/
theorem weightedPositiveMulX_inclusion (s k : ℕ) (x : lp.DegreeWeightedL2 s) :
    lp.degreeWeightedInclusion s (weightedPositiveMulX s k x) =
      boundedPositiveMulX k (lp.degreeWeightedInclusion s x) := by
  ext i
  rw [lp.degreeWeightedInclusion_apply]
  change (lp.degreeWeightedShiftRight s (lp.degreeWeightedDiagonal s _ _ _ x)).1 i +
    (lp.degreeWeightedShiftLeft s (lp.degreeWeightedDiagonal s _ _ _ x)).1 i = _
  cases i with
  | zero => simp [lp.degreeWeightedShiftRight_zero, lp.degreeWeightedShiftLeft_apply,
      lp.degreeWeightedDiagonal_apply, boundedPositiveMulX_zero]
  | succ i => simp [lp.degreeWeightedShiftRight_succ, lp.degreeWeightedShiftLeft_apply,
      lp.degreeWeightedDiagonal_apply, boundedPositiveMulX_succ, Nat.add_assoc]

/-- Weighted ultraspherical multiplication agrees with polynomial multiplication. -/
theorem weightedPositiveMulX_coefficient (s k : ℕ) (p : ℝ[X]) :
    weightedPositiveMulX s k ((ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s p) =
      (ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s (X * p) := by
  apply lp.degreeWeightedInclusion_injective s
  rw [weightedPositiveMulX_inclusion, Module.Basis.degreeWeightedCoefficient_inclusion,
    Module.Basis.degreeWeightedCoefficient_inclusion, boundedPositiveMulX_coefficientLp]

/-- Successive positive ultraspherical conversion steps. -/
def weightedPositiveRaise (s k : ℕ) : ℕ → (lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s)
  | 0 => 1
  | d + 1 => (weightedPositiveConversion s (k + d)).comp (weightedPositiveRaise s k d)

/-- Successive conversions give the polynomial coordinates at the final level. -/
theorem weightedPositiveRaise_coefficient (s k d : ℕ) (p : ℝ[X]) :
    weightedPositiveRaise s k d ((ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s p) =
      (ultrasphericalBasis (k + d + 1)).degreeWeightedCoefficient s p := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [weightedPositiveRaise, comp_apply, ih, weightedPositiveConversion_coefficient]
    congr 2

/-- Any nonempty positive conversion chain is compact. -/
theorem isCompactOperator_weightedPositiveRaise (s k d : ℕ) :
    IsCompactOperator (weightedPositiveRaise s k (d + 1)) :=
  (isCompactOperator_weightedPositiveConversion s (k + d)).comp_clm (weightedPositiveRaise s k d)

/-- Polynomial functional calculus of weighted ultraspherical multiplication by x. -/
def weightedPositivePolynomialMultiplier (s k : ℕ) (p : ℝ[X]) :
    lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  aeval (weightedPositiveMulX s k) (p.map Complex.ofRealHom)

/-- Weighted ultraspherical functional calculus gives polynomial multiplication. -/
theorem weightedPositivePolynomialMultiplier_coefficient (s k : ℕ) (p q : ℝ[X]) :
    weightedPositivePolynomialMultiplier s k p
        ((ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s q) =
      (ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s (p * q) := by
  unfold weightedPositivePolynomialMultiplier
  induction p using Polynomial.induction_on generalizing q with
  | C a =>
    rw [Polynomial.map_C, Polynomial.aeval_C]
    change (a : ℂ) • (ultrasphericalBasis (k + 1)).degreeWeightedCoefficient s q = _
    rw [← Module.Basis.degreeWeightedCoefficient_smul, smul_eq_C_mul]
  | add p r hp hr =>
    rw [Polynomial.map_add, map_add, add_apply, hp, hr, add_mul,
      Module.Basis.degreeWeightedCoefficient_add]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, Polynomial.map_mul, map_mul, mul_apply_eq_comp,
      Polynomial.map_X, aeval_X, weightedPositiveMulX_coefficient, ih]
    simp only [mul_assoc]

/-- Polynomial functional calculus of weighted Chebyshev multiplication by x. -/
def weightedChebyshevPolynomialMultiplier (s : ℕ) (p : ℝ[X]) :
    lp.DegreeWeightedL2 s →L[ℂ] lp.DegreeWeightedL2 s :=
  aeval (weightedChebyshevMulX s) (p.map Complex.ofRealHom)

/-- Weighted Chebyshev functional calculus gives polynomial multiplication. -/
theorem weightedChebyshevPolynomialMultiplier_coefficient (s : ℕ) (p q : ℝ[X]) :
    weightedChebyshevPolynomialMultiplier s p
        (chebyshevBasis.degreeWeightedCoefficient s q) =
      chebyshevBasis.degreeWeightedCoefficient s (p * q) := by
  unfold weightedChebyshevPolynomialMultiplier
  induction p using Polynomial.induction_on generalizing q with
  | C a =>
    rw [Polynomial.map_C, Polynomial.aeval_C]
    change (a : ℂ) • chebyshevBasis.degreeWeightedCoefficient s q = _
    rw [← Module.Basis.degreeWeightedCoefficient_smul, smul_eq_C_mul]
  | add p r hp hr =>
    rw [Polynomial.map_add, map_add, add_apply, hp, hr, add_mul,
      Module.Basis.degreeWeightedCoefficient_add]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, Polynomial.map_mul, map_mul, mul_apply_eq_comp,
      Polynomial.map_X, aeval_X, weightedChebyshevMulX_coefficient, ih]
    simp only [mul_assoc]

end Polynomial.Chebyshev
