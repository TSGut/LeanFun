/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.ContinuousJacobiVolterraInjectivity
public import LeanFun.Mathlib.Analysis.IntegralEq.JacobiLocalIntegrability
public import LeanFun.Mathlib.Analysis.IntegralEq.PolynomialVolterraUniqueness
@[expose] public noncomputable section
/-! # First-kind uniqueness in the weighted Jacobi realization

Compact interval tests turn a zero weak output into a zero physical Volterra
primitive. Local integrability and a countable interval cover then give
injectivity without imposing unweighted global integrability.
Reference: Linz (1985), first-kind Volterra uniqueness; Gutleb's thesis, §2.7.
-/

open MeasureTheory Polynomial Set
open scoped ENNReal InnerProductSpace
namespace MvPolynomial
local notation "μ" => unitJacobiMeasure 1 0
local notation "ν" => volume.restrict (Icc (0 : ℝ) 1)
/-- A zero weighted output gives a zero physical primitive on every interior interval. -/
theorem polynomialVolterraIntegral_eq_zero_of_jacobiVolterraL2Operator_eq_zero
    (K : MvPolynomial (Fin 2) ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ z ∈ Real.volterraTriangle, |eval z K| ≤ M)
    (f : Lp ℝ 2 μ) (hz : jacobiVolterraL2Operator K hM hbnd f = 0)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ x : Icc (0 : ℝ) b, Real.volterraIntegral
      (.ofIntegrableOnPolynomial K (integrableOn_coe_jacobiOneZeroLp f hb1) x) = 0 := by
  have hz' : Real.jacobiVolterraL2Operator K.continuous_eval.continuousOn hM hbnd f = 0 := by
    rwa [Real.jacobiVolterraL2Operator_polynomial]
  intro x
  simpa only [Real.VolterraIntegralInput.ofIntegrableOnPolynomial,
    Real.VolterraIntegralInput.ofJacobiOneZeroLp,
    Real.VolterraIntegralInput.ofContinuousKernel, Real.volterraIntegral_ofKernel] using
    Real.volterraIntegral_eq_zero_of_jacobiVolterraL2Operator_eq_zero
      (fun z ↦ eval z K) K.continuous_eval.continuousOn hM hbnd f hz' hb0 hb1 x

end MvPolynomial
namespace MvPolynomial
local notation "μ" => unitJacobiMeasure 1 0
/-- A nonvanishing polynomial kernel diagonal makes the weighted zero-output input zero. -/
theorem eq_zero_of_jacobiVolterraL2Operator_eq_zero
    (K : MvPolynomial (Fin 2) ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ z ∈ Real.volterraTriangle, |eval z K| ≤ M)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (f : Lp ℝ 2 μ) (hz : jacobiVolterraL2Operator K hM hbnd f = 0) : f = 0 := by
  have hlocal (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
      (fun x ↦ f x) =ᵐ[volume.restrict (Icc 0 b)] 0 :=
    ae_eq_zero_of_integrableOn_polynomialVolterraIntegral_eq_zero hb0
      (integrableOn_coe_jacobiOneZeroLp f hb1)
      (fun x hx ↦ hdiag x ⟨hx.1,hx.2.trans hb1.le⟩)
      (polynomialVolterraIntegral_eq_zero_of_jacobiVolterraL2Operator_eq_zero
        K hM hbnd f hz hb0 hb1)
  have hq (q : ℚ) : ∀ᵐ x ∂volume,
      0 < (q : ℝ) → (q : ℝ) < 1 → x ∈ Icc 0 (q : ℝ) → f x = 0 := by
    by_cases h0 : 0 < (q : ℝ)
    · by_cases h1 : (q : ℝ) < 1
      · have h := (ae_restrict_iff' measurableSet_Icc).mp (hlocal q h0 h1)
        filter_upwards [h] with x hx
        exact fun _ _ hmem ↦ hx hmem
      · exact Filter.Eventually.of_forall (fun x _ h ↦ (h1 h).elim)
    · exact Filter.Eventually.of_forall (fun x h ↦ (h0 h).elim)
  have hall : ∀ᵐ x ∂volume, ∀ q : ℚ,
      0 < (q : ℝ) → (q : ℝ) < 1 → x ∈ Icc 0 (q : ℝ) → f x = 0 :=
    ae_all_iff.mpr hq
  apply Lp.ext
  have hz' := ae_unitJacobiMeasure_one_zero_iff.mp (Lp.coeFn_zero ℝ 2 μ)
  apply ae_unitJacobiMeasure_one_zero_iff.mpr
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Icc,
    ((volume.restrict (Icc (0 : ℝ) 1)).ae_ne 1), hz'] with x hx hxi hx1 hz'
  obtain ⟨q,hxq,hq1⟩ := exists_rat_btwn (lt_of_le_of_ne hxi.2 hx1)
  rw [hz']
  exact hx q (by linarith [hxi.1]) hq1 ⟨hxi.1,hxq.le⟩
/-- The weighted first-kind Volterra realization is injective for a nonvanishing diagonal. -/
theorem injective_jacobiVolterraL2Operator
    (K : MvPolynomial (Fin 2) ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ z ∈ Real.volterraTriangle, |eval z K| ≤ M)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) :
    Function.Injective (jacobiVolterraL2Operator K hM hbnd) := by
  intro f g h
  apply sub_eq_zero.mp
  apply eq_zero_of_jacobiVolterraL2Operator_eq_zero K hM hbnd hdiag
  rw [map_sub, h, sub_self]
end MvPolynomial
