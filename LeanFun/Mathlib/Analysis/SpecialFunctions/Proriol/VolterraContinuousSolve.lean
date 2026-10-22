/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraContinuousBridge
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraLimitStability
public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousJacobiVolterraInjectivity

/-! # Nonpolynomial first-kind Volterra solves

Absolutely continuous kernel slices with a uniform derivative bound give
uniqueness. Uniform physical approximation and operator-norm consistency then
give invertibility and stable finite solves. Reference: Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
open Polynomial Set Filter ContinuousLinearMap
open scoped Topology
namespace Real
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2
variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
  {C : ℝ}
  (hAC : ∀ x ∈ Icc (0 : ℝ) 1,
    AbsolutelyContinuousOnInterval (fun y ↦ K ![x,y]) 0 x)
  (hder : ∀ x ∈ Icc (0 : ℝ) 1,
    ∃ g : IntegrableDerivative (fun t ↦ K ![x,t]) (MeasureTheory.volume.restrict (uIcc 0 x)),
      ∀ᵐ y ∂MeasureTheory.volume.restrict (uIcc 0 x), ‖g y‖ ≤ C*|K ![x,x]|)
  (hd : ∀ x ∈ Icc (0 : ℝ) 1, K ![x,x] ≠ 0)
  (p : ℕ → MvPolynomial (Fin 2) ℝ) {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n)
  (herr : ∀ n z, z ∈ volterraTriangle → |MvPolynomial.eval z (p n)-K z| ≤ e n)
  (hte : Tendsto e atTop (𝓝 0))
  (A : H →L[ℝ] H)
  (hA : Tendsto (fun n ↦ MvPolynomial.volterraPreconditionedL2 (p n)) atTop (𝓝 A))

include hK hAC hder hd he herr hte hA in
/-- A regular continuous kernel with nonvanishing diagonal gives an invertible raw limit
and uniformly stable leading sections, for either diagonal sign. -/
theorem isUnit_and_stable_continuousVolterra :
    IsUnit A ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N in atTop,
      IsUnit (coerciveFiniteSection (lp.initialL2Projection N) A) ∧
      ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N) A)‖ ≤ B := by
  obtain ⟨M,hb⟩ := MvPolynomial.isCompact_volterraTriangle.exists_bound_of_continuousOn hK
  have bK : ∀ z ∈ volterraTriangle, |K z| ≤ |M| :=
    fun z hz ↦ (hb z hz).trans (le_abs_self M)
  have bp (n : ℕ) (z : Fin 2 → ℝ) (hz : z ∈ volterraTriangle) :
      |MvPolynomial.eval z (p n)| ≤ |M|+e n := by
    have h := abs_add_le (MvPolynomial.eval z (p n)-K z) (K z)
    rw [sub_add_cancel] at h
    linarith [herr n z hz,bK z hz]
  have bridge := jacobiVolterraL2Operator_raw_limit hK (abs_nonneg M) bK p
    (fun n ↦ add_nonneg (abs_nonneg M) (he n)) bp he herr hte A hA
  have hinj : Function.Injective A := by
    intro u v huv
    apply shiftedJacobiOneZeroSynthesis_injective
    apply injective_jacobiVolterraL2Operator K hK (abs_nonneg M) bK hAC hder hd
    have hu := congrArg (fun T ↦ T u) bridge
    have hv := congrArg (fun T ↦ T v) bridge
    simp only [comp_apply] at hu hv
    rw [← hu,← hv,huv]
  have hmem (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (fun _ : Fin 2 ↦ x) ∈ volterraTriangle := ⟨hx,hx.1,le_rfl⟩
  have hpair (x : ℝ) : (![x,x] : Fin 2 → ℝ) = (fun _ ↦ x) := by
    funext i; fin_cases i <;> rfl
  exact MvPolynomial.isUnit_and_stable_volterra_limit K p
    (hK.comp (by fun_prop) hmem)
    (fun x hx ↦ by simpa only [hpair] using hd x hx)
    he (fun n x hx ↦ herr n _ (hmem x hx)) hte A hA hinj

include hK hAC hder hd he herr hte hA in
/-- Polynomial kernel approximants and data approximants can be refined together with the cutoff. -/
theorem tendsto_continuousVolterra_section_solution
    (g : H) (gN : ℕ → H) (hg : Tendsto gN atTop (𝓝 g)) :
    Tendsto (fun N ↦ Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
      (MvPolynomial.volterraPreconditionedL2 (p N))) (lp.initialL2Projection N (gN N)))
      atTop (𝓝 (Ring.inverse A g)) := by
  obtain ⟨hu,B,hB,hs⟩ := isUnit_and_stable_continuousVolterra hK hAC hder hd p he herr hte A hA
  apply lp.tendsto_approximateCoerciveFiniteSection_solution A _ hA hs (Ring.inverse A g) gN
  have hsolve : A (Ring.inverse A g) = g :=
    congrArg (fun T : H →L[ℝ] H ↦ T g) (Ring.mul_inverse_cancel A hu)
  simpa only [hsolve] using hg

include hK hAC hder hd he hte in
/-- Summable polynomial operator majorants discharge norm consistency for continuous-kernel
first-kind solves; physical uniform approximation is still a separate assumption. -/
theorem isUnit_and_stable_continuousVolterra_series
    (hm : Summable (fun n ↦ MvPolynomial.volterraKernelMajorant (p n)))
    (hpartial : ∀ n z, z ∈ volterraTriangle →
      |MvPolynomial.eval z (∑ i ∈ Finset.range n, p i)-K z| ≤ e n) :
    IsUnit (∑' n, MvPolynomial.volterraPreconditionedL2 (p n)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N in atTop,
        IsUnit (coerciveFiniteSection (lp.initialL2Projection N)
          (∑' n, MvPolynomial.volterraPreconditionedL2 (p n))) ∧
        ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
          (∑' n, MvPolynomial.volterraPreconditionedL2 (p n)))‖ ≤ B :=
  isUnit_and_stable_continuousVolterra hK hAC hder hd
    (fun n ↦ ∑ i ∈ Finset.range n, p i) he hpartial hte _
    (MvPolynomial.tendsto_volterraPreconditionedL2_sum_of_majorant p hm)
end Real
