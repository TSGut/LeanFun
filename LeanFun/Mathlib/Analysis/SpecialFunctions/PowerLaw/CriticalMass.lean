/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerSymmetric

/-! # An exact Schur weight at the critical power-law parameters

At `α + λ = -1/2`, the auxiliary weight `(1-x²)^(α/2)` has an exactly
computable weighted row integral. This uses the Gauss binomial specialization
(DLMF 15.4.6) of the power-law formula of Gutleb–Carrillo–Olver,
arXiv:2011.00045, Section 2. The identity holds in the open interval;
the auxiliary weight is not asserted to belong to the underlying L² space.
-/

public section
open Set Polynomial MeasureTheory
namespace Real


/-- The constant in the critical Schur identity is strictly positive. -/
theorem powerLaw_critical_constant_pos {α : ℝ} (hα : -1 < α) (hα0 : α < 0) :
    0 < Gamma ((α+1)/2)*Gamma (-α/2)/Gamma (1/2) := by
  exact div_pos (mul_pos (Gamma_pos_of_pos (by linarith))
    (Gamma_pos_of_pos (by linarith))) (Gamma_pos_of_pos (by norm_num))


end Real
