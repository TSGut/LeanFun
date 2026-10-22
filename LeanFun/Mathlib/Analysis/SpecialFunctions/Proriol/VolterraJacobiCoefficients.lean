/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraJacobi
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The shifted Jacobi extension/marginal diagonal

The diagonal is exact on finitely supported coefficients; the endpoint factor
is not absorbed into it. Reference: Gutleb–Olver, arXiv:1906.03907,
Section 3.1; Gutleb's thesis, Section 2.3.
-/

@[expose] public noncomputable section
namespace MvPolynomial
open Polynomial

/-- Extension followed by the endpoint-factor-free marginal, in shifted
Jacobi `(1,0)` coordinates. -/
def volterraJacobiDiagonal : (ℕ →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun n ↦ Finsupp.single n
    ((-1 : ℝ)^n / ((n : ℝ)+1)))

/-- Exact diagonal columns with zero-based indices. -/
theorem volterraJacobiDiagonal_single (n : ℕ) (a : ℝ) :
    volterraJacobiDiagonal (Finsupp.single n a) =
      Finsupp.single n (a * ((-1 : ℝ)^n / ((n : ℝ)+1))) := by
  simp [volterraJacobiDiagonal, Finsupp.linearCombination_single]

/-- Diagonal coefficient assembly agrees with the actual extension/marginal
composition for every finitely supported input. -/
theorem triangleMarginal_extendY_linearCombination (c : ℕ →₀ ℝ) (x : ℝ) :
    triangleMarginal (triangleExtendY (Finsupp.linearCombination ℝ
      (shiftedJacobi 1 0) c)) x =
      (1-x) * (Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
        (volterraJacobiDiagonal c)).eval x := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd, mul_add]
  | single n a =>
    rw [Finsupp.linearCombination_single, map_smul, map_smul, Pi.smul_apply,
      smul_eq_mul, triangleMarginal_extendY_shiftedJacobi,
      volterraJacobiDiagonal_single, Finsupp.linearCombination_single]
    simp only [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    ring

end MvPolynomial
