/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerSymmetric
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-! # Approximation for weighted power-law operators

Uniform approximation of the continuous amplitude gives locally uniform output
approximation, including parameters outside the polynomial compatibility regime.
The weight itself may be singular at the endpoints. Reference:
Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open MeasureTheory Set Polynomial Filter
open scoped Topology
namespace Real



end Real
