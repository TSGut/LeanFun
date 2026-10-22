/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Approximation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerEndpoint

/-! # Closed-interval estimates for weighted power-law integrals

The combined endpoint exponent is kept explicit. Uniform mass estimates are
provided separately for nonnegative kernel exponents and bounded Gegenbauer
weights. Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open MeasureTheory Set Polynomial Filter
open scoped Topology
namespace Real


end Real
