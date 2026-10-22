/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Basic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Measure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Mass

/-! # Weighted power-law endpoint integrals

At the right endpoint the power kernel shifts one Jacobi exponent. The
integrability conditions involve the combined endpoint exponent, not just the
interior singularity exponent. Reference: Gutleb–Carrillo–Olver,
arXiv:2011.00045, Section 2; the Beta integral in DLMF 5.12.1.
-/

public section
open MeasureTheory Set Polynomial
namespace Real


end Real
