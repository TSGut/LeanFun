/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClosedInterval

/-! # Uniform mass bounds with singular kernels and singular endpoint weights

Compare the product of two negative powers with their combined power at the
smaller base. Three translated power kernels give a uniform integrable majorant.
The constants are not claimed sharp. Reference: Gutleb–Carrillo–Olver,
arXiv:2011.00045, Section 2 (weighted power-law operator).
-/

@[expose] public noncomputable section
open MeasureTheory Set Polynomial Filter
open scoped Topology
namespace Real


end Real
