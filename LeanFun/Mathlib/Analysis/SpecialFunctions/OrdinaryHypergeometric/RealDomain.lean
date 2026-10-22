/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.Domain
public import Mathlib.Analysis.Complex.Basic
/-! # Real and complex classical Gauss values
Natural-order convergence preserves conditional and terminating cases.
Reference: DLMF 15.2.1, 15.2.4--5.
-/
@[expose] public noncomputable section
open Polynomial Filter
open scoped Topology
namespace GaussParameters
private theorem ofReal_pochhammer (a : ℝ) (n : ℕ) :
    (((ascPochhammer ℝ n).eval a : ℝ) : ℂ) = (ascPochhammer ℂ n).eval (a : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ascPochhammer_succ_eval, ih]

/-- Real admissible parameters remain admissible over the complex numbers. -/
def toComplex (p : GaussParameters ℝ) : GaussParameters ℂ :=
  ⟨p.a, p.b, p.c, fun n hc ↦ by
    have hc' : (ascPochhammer ℝ n).eval p.c = 0 := by
      apply Complex.ofReal_injective
      simpa only [ofReal_pochhammer, Complex.ofReal_zero] using hc
    have h := congrArg Complex.ofReal (p.denominator n hc')
    simpa only [Complex.ofReal_mul, ofReal_pochhammer, Complex.ofReal_zero] using h⟩

/-- Embedding real data commutes with every classical Gauss coefficient. -/
theorem coefficient_toComplex (p : GaussParameters ℝ) (n : ℕ) :
    ordinaryHypergeometricCoefficientOn p.toComplex n =
      ((ordinaryHypergeometricCoefficientOn p n : ℝ) : ℂ) := by
  classical
  simp only [ordinaryHypergeometricCoefficientOn, GaussParameters.toComplex,
    ← ofReal_pochhammer, ← Complex.ofReal_mul, Complex.ofReal_eq_zero]
  split_ifs <;> simp only [Complex.ofReal_zero, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_natCast]

end GaussParameters

/-- Real natural-order convergence gives complex natural-order convergence. -/
def GaussSeriesPoint.toComplex (p : GaussParameters ℝ) (z : GaussSeriesPoint p) :
    GaussSeriesPoint p.toComplex := by
  refine ⟨(z.val : ℂ), ((ordinaryHypergeometricOn p z : ℝ) : ℂ), ?_⟩
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_ordinaryHypergeometricOn p z)
  simpa only [Function.comp_def, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, GaussParameters.coefficient_toComplex] using h

/-- Real and complex classical Gauss values agree, including conditional and terminating sums. -/
theorem Complex.ofReal_ordinaryHypergeometric (p : GaussParameters ℝ)
    (z : GaussSeriesPoint p) :
    ((ordinaryHypergeometricOn p z : ℝ) : ℂ) =
      ordinaryHypergeometricOn p.toComplex (z.toComplex p) := by
  symm
  apply ordinaryHypergeometricOn_eq_of_tendsto
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_ordinaryHypergeometricOn p z)
  simpa only [GaussSeriesPoint.toComplex, Function.comp_def, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow, GaussParameters.coefficient_toComplex] using h
