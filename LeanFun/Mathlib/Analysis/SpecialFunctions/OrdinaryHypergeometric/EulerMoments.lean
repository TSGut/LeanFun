/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Euler Beta moments for the ordinary hypergeometric function

The complex Beta-weighted monomials reproduce the coefficients of Mathlib's
existing `ordinaryHypergeometric`. This is the termwise foundation of Euler's
integral, DLMF 15.6.1, before interchanging an infinite sum with the integral.
The normalization is the ordinary, not regularized, hypergeometric function.
-/

public section
open MeasureTheory Set Polynomial
namespace Complex





end Complex
