/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousJacobiVolterra
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraRawL2Bridge
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraKernelMajorant

/-! # Polynomial approximation identifies continuous-kernel first-kind operators

Uniform physical kernel convergence and preconditioned operator-norm
convergence have separate roles. Reference: Gutleb's thesis, §2.7, Lemma 2.5.
-/

@[expose] public noncomputable section
open Polynomial MeasureTheory Set Filter
open scoped Topology
namespace Real
variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
  {M : ℝ} (hM : 0 ≤ M) (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M)
  (p : ℕ → MvPolynomial (Fin 2) ℝ) {B e : ℕ → ℝ}
  (hB : ∀ n, 0 ≤ B n)
  (bp : ∀ n z, z ∈ volterraTriangle → |MvPolynomial.eval z (p n)| ≤ B n)
  (he : ∀ n, 0 ≤ e n)
  (err : ∀ n z, z ∈ volterraTriangle → |MvPolynomial.eval z (p n)-K z| ≤ e n)
  (hte : Tendsto e atTop (𝓝 0))

include he err hte in
/-- Uniform triangle approximation controls the weighted reflected operator in norm. -/
theorem tendsto_polynomial_jacobiVolterraL2Operator :
    Tendsto (fun n ↦ MvPolynomial.jacobiVolterraL2Operator (p n) (hB n) (bp n))
      atTop (𝓝 (jacobiVolterraL2Operator hK hM bK)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hte
  rw [← jacobiVolterraL2Operator_polynomial]
  exact norm_jacobiVolterraL2Operator_sub_le (p n).continuous_eval.continuousOn
    (hB n) (bp n) hK hM bK (he n) (err n)

include hB bp he err hte in
/-- The full raw operator limit represents the actual continuous-kernel integral,
with the integration diagonal, reflection and endpoint averaging retained. -/
theorem jacobiVolterraL2Operator_raw_limit
    (A : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2)
    (hA : Tendsto (fun n ↦ MvPolynomial.volterraPreconditionedL2 (p n)) atTop (𝓝 A)) :
    shiftedJacobiOneZeroSynthesis.comp (volterraRawDiagonal.comp A) =
      (jacobiVolterraL2Operator hK hM bK).comp shiftedJacobiOneZeroSynthesis := by
  apply ContinuousLinearMap.ext
  intro u
  have hc : Continuous (fun T : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 ↦
      shiftedJacobiOneZeroSynthesis (volterraRawDiagonal (T u))) := by fun_prop
  have hd : Continuous (fun T : Lp ℝ 2 (unitJacobiMeasure 1 0) →L[ℝ]
      Lp ℝ 2 (unitJacobiMeasure 1 0) ↦ T (shiftedJacobiOneZeroSynthesis u)) := by fun_prop
  have hl := hc.continuousAt.tendsto.comp hA
  have hr := hd.continuousAt.tendsto.comp
    (tendsto_polynomial_jacobiVolterraL2Operator hK hM bK p hB bp he err hte)
  apply tendsto_nhds_unique hl
  apply hr.congr'
  exact Eventually.of_forall (fun n ↦
    (congrArg (fun T ↦ T u)
      (MvPolynomial.jacobiVolterraL2Operator_raw_synthesis (p n) (hB n) (bp n))).symm)

end Real
namespace Real
/-- A majorized polynomial kernel expansion represents the actual continuous-kernel integral.
Uniform physical convergence is stated separately from the coefficient majorant. -/
theorem jacobiVolterraL2Operator_raw_series
    {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
    {M : ℝ} (hM : 0 ≤ M) (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M)
    (p : ℕ → MvPolynomial (Fin 2) ℝ)
    (hm : Summable (fun n ↦ MvPolynomial.volterraKernelMajorant (p n)))
    {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n)
    (herr : ∀ n z, z ∈ volterraTriangle →
      |MvPolynomial.eval z (∑ i ∈ Finset.range n, p i)-K z| ≤ e n)
    (hte : Tendsto e atTop (𝓝 0)) :
    shiftedJacobiOneZeroSynthesis.comp (volterraRawDiagonal.comp
      (∑' n, MvPolynomial.volterraPreconditionedL2 (p n))) =
      (jacobiVolterraL2Operator hK hM bK).comp shiftedJacobiOneZeroSynthesis := by
  have hb (n : ℕ) (z : Fin 2 → ℝ) (hz : z ∈ volterraTriangle) :
      |MvPolynomial.eval z (∑ i ∈ Finset.range n, p i)| ≤ M+e n := by
    have h := abs_add_le (MvPolynomial.eval z (∑ i ∈ Finset.range n, p i)-K z) (K z)
    rw [sub_add_cancel] at h
    linarith [herr n z hz,bK z hz]
  exact jacobiVolterraL2Operator_raw_limit hK hM bK
    (fun n ↦ ∑ i ∈ Finset.range n, p i) (fun n ↦ add_nonneg hM (he n)) hb he herr hte _
    (MvPolynomial.tendsto_volterraPreconditionedL2_sum_of_majorant p hm)
end Real
