/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Weight
public import LeanFun.Mathlib.Analysis.Calculus.Deriv.OpenDomain
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer.DifferentialEquation
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Weighted Gegenbauer primitives

The Sturm--Liouville form of the Gegenbauer equation yields a primitive that
vanishes at both endpoints in the orthogonality range. DLMF 18.9.20.
-/

public section
open Set Real
namespace Polynomial




/-- Raising the parameter multiplies the classical weight by its quadratic factor. -/
theorem gegenbauerWeight_add_one (lam : ℝ) (x : Ioo (-1 : ℝ) 1) :
    (gegenbauerWeight (lam + 1) x : ℝ) =
      (1 - (x : ℝ) ^ 2) * (gegenbauerWeight lam x : ℝ) := by
  change (jacobiWeight (lam+1-1/2) (lam+1-1/2) x : ℝ) =
    (1-(x : ℝ)^2)*(jacobiWeight (lam-1/2) (lam-1/2) x : ℝ)
  rw [show lam+1-1/2 = (lam-1/2)+1 by ring]
  exact jacobiWeight_add_one _ _ x

/-- Pearson identity as an actual derivative on the open interval. -/
theorem hasDerivAt_gegenbauerWeight_add_one (lam : ℝ) (x : Ioo (-1 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (gegenbauerWeight (lam + 1) y : ℝ))
      (-(2 * lam + 1) * (x : ℝ) * (gegenbauerWeight lam x : ℝ)) x := by
  have he : lam + 1 - 1 / 2 = (lam - 1 / 2) + 1 := by ring
  change HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ (fun y ↦ (jacobiWeight (lam + 1 - 1 / 2)
    (lam + 1 - 1 / 2) y : ℝ)) _ x
  rw [he]
  convert hasDerivAt_jacobiWeight_add_one (lam - 1 / 2) (lam - 1 / 2) x using 1
  change -(2 * lam + 1) * (x : ℝ) * (jacobiWeight (lam - 1 / 2) (lam - 1 / 2) x : ℝ) = _
  ring

/-- The weighted Gegenbauer primitive on its classical open domain. -/
theorem hasDerivAt_gegenbauerWeight_mul_derivative (lam : ℝ) (n : ℕ)
    (x : Ioo (-1 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (gegenbauerWeight (lam + 1) y : ℝ) *
        (gegenbauer lam n).derivative.eval (y : ℝ))
      (-((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        (gegenbauerWeight lam x : ℝ) * (gegenbauer lam n).eval (x : ℝ)) x := by
  have h := (hasDerivAt_gegenbauerWeight_add_one lam x).mul
    ⟨_, fun _ ↦ rfl, (gegenbauer lam n).derivative.hasDerivAt (x : ℝ)⟩
  have he := congrArg (fun p : ℝ[X] ↦ p.eval (x : ℝ)) (gegenbauer_differentialEquation lam n)
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_one, eval_X, eval_zero] at he
  convert h using 1
  rw [gegenbauerWeight_add_one]
  linear_combination -(gegenbauerWeight lam x : ℝ) * he

end Polynomial
