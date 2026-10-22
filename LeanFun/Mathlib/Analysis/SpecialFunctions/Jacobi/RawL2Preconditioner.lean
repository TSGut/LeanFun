/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2Multiplication
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraFirstKind

/-! # Exact reflected Jacobi preconditioning on raw coefficients

The reflection is essential: D H = (I-J) D, with alternating integration
weights D_n=(-1)^n/(n+1). Reference: Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
namespace Polynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2

/-- The first row of the reflected conjugate. -/
theorem reflectedJacobiOneZeroL2_apply_zero (u : H) :
    reflectedJacobiOneZeroL2 u 0 = (2/3 : ℝ)*u 0+(1/12 : ℝ)*u 1 := by
  simp only [reflectedJacobiOneZeroL2, shiftedJacobiToeplitzPart,
    reflectedJacobiOneZeroCorrection, ContinuousLinearMap.comp_apply,
    add_apply, sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_add, lp.coeFn_sub,
    lp.coeFn_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    LinearIsometry.coe_toContinuousLinearMap, lp.forwardShiftL2_zero,
    lp.backwardShiftL2_apply, lp.reciprocalAffineDiagonal_apply]
  norm_num
  ring

/-- The remaining rows of the reflected conjugate. -/
theorem reflectedJacobiOneZeroL2_apply_succ (u : H) (n : ℕ) :
    reflectedJacobiOneZeroL2 u (n+1) =
      (((n : ℝ)+2)^2/(2*(n+1)*(2*n+3)))*u n +
      (1/2+1/(2*(2*n+3)*(2*n+5)))*u (n+1) +
      (((n : ℝ)+2)^2/(2*(n+3)*(2*n+5)))*u (n+2) := by
  simp only [reflectedJacobiOneZeroL2, shiftedJacobiToeplitzPart,
    reflectedJacobiOneZeroCorrection, ContinuousLinearMap.comp_apply,
    add_apply, sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_add, lp.coeFn_sub,
    lp.coeFn_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    LinearIsometry.coe_toContinuousLinearMap, lp.forwardShiftL2_succ,
    lp.backwardShiftL2_apply, lp.reciprocalAffineDiagonal_apply,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  ring

/-- The integration diagonal viewed as a bounded endomorphism of raw ℓ². -/
def volterraRawDiagonal : H →L[ℝ] H :=
  (lp.reciprocalAffineDiagonal 1 1 (by norm_num)).comp
    lp.alternatingL2Isometry.toContinuousLinearEquiv.toContinuousLinearMap

/-- The raw diagonal has the same entries as the weighted-space equivalence. -/
@[simp] theorem volterraRawDiagonal_apply (u : H) (n : ℕ) :
    volterraRawDiagonal u n = ((-1 : ℝ)^n/((n : ℝ)+1))*u n := by
  simp only [volterraRawDiagonal, ContinuousLinearMap.comp_apply,
    lp.reciprocalAffineDiagonal_apply]
  simp only [Nat.cast_one, one_mul, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  change ((n : ℝ)+1)⁻¹*((-1 : ℝ)^n*u n) = _
  ring

/-- Agreement with the first-kind diagonal into the weighted range space. -/
theorem volterraRawDiagonal_eq_weighted (u : H) (n : ℕ) :
    volterraRawDiagonal u n = (MvPolynomial.volterraJacobiL2Equiv u).1 n := by
  rw [volterraRawDiagonal_apply, MvPolynomial.volterraJacobiL2Equiv_apply]

/-- The reflected preconditioner satisfies its defining diagonal intertwining identity. -/
theorem volterraRawDiagonal_mul_reflectedJacobiOneZeroL2 :
    volterraRawDiagonal*reflectedJacobiOneZeroL2 =
      (1-shiftedJacobiOneZeroL2)*volterraRawDiagonal := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext i
  change volterraRawDiagonal (reflectedJacobiOneZeroL2 u) i =
    volterraRawDiagonal u i-shiftedJacobiOneZeroL2 (volterraRawDiagonal u) i
  cases i with
  | zero =>
    rw [volterraRawDiagonal_apply, reflectedJacobiOneZeroL2_apply_zero,
      shiftedJacobiOneZeroL2_apply_zero]
    simp only [volterraRawDiagonal_apply, shiftedJacobiOneZeroDiag, shiftedJacobiOneZeroLower]
    norm_num
    ring
  | succ n =>
    rw [volterraRawDiagonal_apply, reflectedJacobiOneZeroL2_apply_succ,
      shiftedJacobiOneZeroL2_apply_succ]
    simp only [volterraRawDiagonal_apply, shiftedJacobiOneZeroUpper,
      shiftedJacobiOneZeroDiag, shiftedJacobiOneZeroLower, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, pow_succ]
    field_simp
    ring

end Polynomial
