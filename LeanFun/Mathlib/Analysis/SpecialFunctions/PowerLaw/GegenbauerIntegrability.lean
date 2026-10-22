/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Basic
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Measure
public import LeanFun.Mathlib.RingTheory.Polynomial.Gegenbauer
import Mathlib.Topology.Algebra.Polynomial

/-! # Weighted power-law integrability at interior points

Separate the kernel singularity from the endpoint singularities of the
Gegenbauer weight. Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045,
Section 2. Interior and endpoint exponent conditions are distinct.
-/

public section
open MeasureTheory Set Polynomial
namespace Real


end Real
