/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.Noncompact
public import LeanFun.Mathlib.Analysis.IntegralEq.WeakKernel

/-! # Classical endpoint tests for power-law kernels

Positive widths and admissible weights are typed. Weak pairings have their
integrability certified; agreement with a singular power kernel is asserted
only off the diagonal. Reference: Gutleb–Carrillo–Olver, arXiv:2011.00045, §2.
-/
@[expose] public noncomputable section
open MeasureTheory Set Polynomial Filter
open scoped ENNReal InnerProductSpace Topology
namespace Real

end Real
namespace Real




end Real

namespace Real
theorem not_isCompactOperator_powerLaw_criticalOn
    (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (hc : α.val+lam.val = -(1/2)) (T : PowerLawWeakRealization α.val lam.val) :
    ¬ IsCompactOperator T.val := by
  exact not_isCompactOperator_powerLaw_critical_of_pairing α.property lam.property hc T.val T.property

end Real
