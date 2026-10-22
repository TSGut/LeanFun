/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerHypergeometric
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # The degree-zero power-law integral at the origin

The square substitution reduces the integral to a Beta value. This fixes the
normalizing constant in the symmetric formula of Gutleb–Carrillo–Olver,
arXiv:2011.00045, Section 2.
-/

public section
open Set MeasureTheory Polynomial
namespace Real


end Real
