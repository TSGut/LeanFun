/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.JacobiVolterraL2
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.RawL2Synthesis
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraRawAssembly
/-! # Infinite raw Jacobi synthesis intertwines the Volterra operators

The exact finite Proriol identity extends by continuity to all raw square-
summable inputs. The weighted operator retains reflection and endpoint averaging.
Reference: Gutleb's thesis, §§2.3 and 2.7.
-/

open MeasureTheory Polynomial
open scoped ENNReal
@[expose] public noncomputable section
namespace MvPolynomial
/-- Raw synthesis intertwines the full ordered operator, with its integration
diagonal, and the bounded weighted Volterra realization. -/
theorem jacobiVolterraL2Operator_raw_synthesis (K : MvPolynomial (Fin 2) ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ Real.volterraTriangle, |eval z K| ≤ M) :
    shiftedJacobiOneZeroSynthesis.comp
      (volterraRawDiagonal.comp (volterraPreconditionedL2 K)) =
    (jacobiVolterraL2Operator K hM hb).comp shiftedJacobiOneZeroSynthesis := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro a
  change shiftedJacobiOneZeroSynthesis
      (volterraRawDiagonal (volterraPreconditionedL2 K (lp.single 2 i a))) =
    jacobiVolterraL2Operator K hM hb (shiftedJacobiOneZeroSynthesis (lp.single 2 i a))
  rw [← lp.finsuppL2_single, volterraRawDiagonal_preconditioned_finsupp,
    shiftedJacobiOneZeroSynthesis_finsupp, shiftedJacobiOneZeroSynthesis_finsupp]
  apply (jacobiVolterraL2Operator_polynomial K hM hb _ _ _).symm
  intro x hx
  simpa only [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel] using
    (volterraProriolCoefficients_exact K (Finsupp.single i a) x).symm
end MvPolynomial
