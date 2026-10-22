/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraL2
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraApproximation

/-! # The L² Volterra realization agrees with finite Proriol assembly

The exact bridge includes the physical endpoint factor and reflection. Its
L² coefficients are normalized shifted Legendre coordinates, not the unscaled
shifted-Jacobi coordinates of the intermediate D M_K E map.
Reference: Gutleb–Olver, arXiv:1906.03907, Sections 3.1–3.2.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial Set Filter Real
open scoped ENNReal InnerProductSpace Topology

local instance : IsFiniteMeasure (unitJacobiMeasure 0 0) :=
  isFiniteMeasure_unitJacobiMeasure (by norm_num) (by norm_num)

namespace Real

/-- A physical polynomial integral identity identifies the L² output exactly. -/
theorem volterraL2Operator_polynomial {K : (Fin 2 → ℝ) → ℝ}
    (hK : ContinuousOn K volterraTriangle) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z ∈ volterraTriangle, |K z| ≤ M) (p q : ℝ[X])
    (hq : ∀ x : Icc (0 : ℝ) 1,
      volterraIntegral (.ofContinuous hK p.continuous.continuousOn x) = q.eval (x : ℝ)) :
    volterraL2Operator hK hM hb
      (polynomialToL2 (hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num)) p) =
      polynomialToL2 (hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num)) q := by
  let hm := hasFiniteMoments_unitJacobiMeasure (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0)
  apply ext_inner_left ℝ
  intro g
  have hp := (Measure.quasiMeasurePreserving_snd (μ := unitJacobiMeasure 0 0)
    (ν := unitJacobiMeasure 0 0)).ae_eq_comp (coe_polynomialToL2 hm p)
  have he : (fun z : ℝ × ℝ ↦ volterraL2Kernel K z * (g z.1 * polynomialToL2 hm p z.2)) =ᵐ[(unitJacobiMeasure 0 0).prod (unitJacobiMeasure 0 0)]
      (fun z ↦ volterraL2Kernel K z * (g z.1*p.eval z.2)) := by
    filter_upwards [hp] with z hz
    simp only [Function.comp_apply] at hz
    rw [hz]
  have hi := (integrable_volterraL2_pair hK hM hb (polynomialToL2 hm p) g).congr he
  rw [inner_volterraL2Operator, integral_congr_ae he, integral_prod _ hi, ← integral_const_mul,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_mem_Icc_unitJacobiMeasure 0 0, coe_polynomialToL2 hm q] with x hx hqx
  simp_rw [show ∀ y, volterraL2Kernel K (x,y)*(g x*p.eval y) =
    g x*(volterraL2Kernel K (x,y)*p.eval y) by intro y; ring]
  rw [integral_const_mul, integral_volterraL2Kernel K (fun y ↦ p.eval y) ⟨x,hx⟩
    (intervalIntegrable_volterra hK p.continuous.continuousOn hx)]
  rw [show volterraIntegral (.ofKernel K (fun y ↦ p.eval y)
      (intervalIntegrable_volterra hK p.continuous.continuousOn hx)) = q.eval x from
    hq ⟨x,hx⟩]
  simp only [Real.inner_apply, hqx]
  ring

/-- Every continuous triangle kernel has a finite L² norm certificate. -/
theorem exists_volterraL2_bound {K : (Fin 2 → ℝ) → ℝ}
    (hK : ContinuousOn K volterraTriangle) :
    ∃ (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |K z| ≤ M),
      ‖volterraL2Operator hK hM hb‖ ≤ M ∧ ‖volterraL2CoefficientOperator hK hM hb‖ ≤ M := by
  obtain ⟨M,hb⟩ := MvPolynomial.isCompact_volterraTriangle.exists_bound_of_continuousOn hK
  have hb' : ∀ z ∈ volterraTriangle, |K z| ≤ |M| := fun z hz ↦
    (hb z hz).trans (le_abs_self M)
  exact ⟨|M|, abs_nonneg M, hb', norm_volterraL2Operator_le hK _ hb',
    norm_volterraL2CoefficientOperator_le hK _ hb'⟩

end Real
namespace MvPolynomial

/-- The physical output polynomial reconstructed from finite Proriol Volterra coordinates. -/
def volterraProriolOutput (K : MvPolynomial (Fin 2) ℝ) (c : ℕ →₀ ℝ) : ℝ[X] :=
  Polynomial.X * (Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
    (volterraProriolCoefficients K c)).comp (1-Polynomial.X)

/-- The physical output includes both endpoint multiplication and reflection. -/
theorem eval_volterraProriolOutput (K : MvPolynomial (Fin 2) ℝ) (c : ℕ →₀ ℝ) (x : ℝ) :
    (volterraProriolOutput K c).eval x =
      volterraIntegral (.ofPolynomial K
        (Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c).continuous.locallyIntegrable x) := by
  rw [VolterraIntegralInput.ofPolynomial, volterraIntegral_ofKernel]
  simp only [volterraProriolOutput, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_one]
  exact volterraProriolCoefficients_exact K c x

/-- The bounded L² realization reproduces the existing finite polynomial assembly exactly. -/
theorem volterraL2Operator_proriol (K : MvPolynomial (Fin 2) ℝ) (c : ℕ →₀ ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |eval z K| ≤ M) :
    volterraL2Operator K.continuous_eval.continuousOn hM hb
      (polynomialToL2 (hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num))
        (Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c)) =
      polynomialToL2 (hasFiniteMoments_unitJacobiMeasure (by norm_num) (by norm_num))
        (volterraProriolOutput K c) :=
  volterraL2Operator_polynomial K.continuous_eval.continuousOn hM hb _ _
    (fun x ↦ by
      simpa only [VolterraIntegralInput.ofContinuous, VolterraIntegralInput.ofPolynomial,
        volterraIntegral_ofKernel] using (eval_volterraProriolOutput K c (x : ℝ)).symm)

/-- Normalized L² coordinates of finite assembly agree with the bounded coefficient action. -/
theorem volterraL2CoefficientOperator_proriol (K : MvPolynomial (Fin 2) ℝ) (c : ℕ →₀ ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ volterraTriangle, |eval z K| ≤ M) :
    let b := hilbertBasisShiftedJacobi (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (-1 : ℝ) < 0)
    let hm := hasFiniteMoments_unitJacobiMeasure (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (-1 : ℝ) < 0)
    volterraL2CoefficientOperator K.continuous_eval.continuousOn hM hb
      (b.repr (polynomialToL2 hm (Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c))) =
      b.repr (polynomialToL2 hm (volterraProriolOutput K c)) := by
  dsimp only
  rw [volterraL2CoefficientOperator, HilbertBasis.coefficientOperator_repr,
    volterraL2Operator_proriol]

end MvPolynomial
