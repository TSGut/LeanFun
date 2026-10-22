/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.RealDomain

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.EulerIntegral

/-! # Real and complex Gauss hypergeometric functions

Compatibility of Mathlib's real and complex series and the real Euler integral
(DLMF 15.6.1, in ordinary normalization).
-/

public section
open Polynomial MeasureTheory Set
namespace Complex

/-- Real ascending Pochhammer evaluations embed into the complex ones. -/
theorem ofReal_ascPochhammer_eval (a : ℝ) (n : ℕ) :
    (((ascPochhammer ℝ n).eval a : ℝ) : ℂ) = (ascPochhammer ℂ n).eval (a : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ascPochhammer_succ_eval, ih]


end Complex
namespace Real


end Real
