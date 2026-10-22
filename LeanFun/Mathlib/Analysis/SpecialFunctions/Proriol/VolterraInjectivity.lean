/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.PolynomialVolterraUniqueness
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraCoordinates
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.UnitIntervalCoordinates
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite

/-! # Injectivity of finite Proriol Volterra assembly

The physical uniqueness theorem applies to the exact finite assembly, including
its endpoint factor and output reflection. This concerns finitely supported
inputs; passage to the raw infinite coefficient space is a separate step.
Reference: Gutleb–Olver, Sections 3.1–3.2, and Gutleb's thesis, §2.7.
-/

@[expose] public noncomputable section
open Set Polynomial
namespace MvPolynomial

/-- A finite coefficient input with zero assembled output must vanish. -/
theorem eq_zero_of_volterraProriolCoefficients_eq_zero
    {K : MvPolynomial (Fin 2) ℝ} {b : ℝ} (hb : 0 < b)
    (hdiag : ∀ x ∈ Icc 0 b, eval (fun _ ↦ x) K ≠ 0)
    {c : ℕ →₀ ℝ} (hc : volterraProriolCoefficients K c = 0) : c = 0 := by
  let p := Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c
  have hv : ∀ x ∈ Icc 0 b, Real.volterraIntegral (.ofPolynomial K p.continuous.locallyIntegrable x) = 0 := by
    intro x hx
    rw [Real.VolterraIntegralInput.ofPolynomial, Real.volterraIntegral_ofKernel]
    change (∫ y in (0 : ℝ)..x, eval (![x,y] : Fin 2 → ℝ) K * p.eval y) = 0
    rw [← volterraProriolCoefficients_exact K c x, hc]
    simp
  have he := eq_zero_of_polynomialVolterraIntegral_eq_zero hb p.continuous hdiag hv
  have hp : p = 0 := p.eq_zero_of_infinite_isRoot
    ((Icc_infinite hb).mono (fun x hx ↦ he x hx))
  let B := shiftedJacobiBasis (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0)
  have hB : shiftedJacobi 1 0 = B := by
    funext n
    exact (shiftedJacobiBasis_apply _ _ n).symm
  have hl : LinearIndependent ℝ (shiftedJacobi 1 0) := by
    rw [hB]
    exact B.linearIndependent
  apply hl.finsuppLinearCombination_injective
  simpa only [map_zero] using hp

/-- Exact polynomial Volterra assembly is injective for a nonvanishing diagonal. -/
theorem injective_volterraProriolCoefficients
    {K : MvPolynomial (Fin 2) ℝ} {b : ℝ} (hb : 0 < b)
    (hdiag : ∀ x ∈ Icc 0 b, eval (fun _ ↦ x) K ≠ 0) :
    Function.Injective (volterraProriolCoefficients K) := by
  intro c d h
  apply sub_eq_zero.mp
  apply eq_zero_of_volterraProriolCoefficients_eq_zero hb hdiag
  rw [map_sub, h, sub_self]

end MvPolynomial
