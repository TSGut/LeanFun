/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.UnweightedNorm
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ExtensionCoefficients

/-! # Finite moment formulas for every Proriol extension entry

The formulas use coefficient sums and a positive denominator, without integral
or abstract basis-coordinate operations. They do not yet simplify the Jacobi
columns to the closed-form rational entries or prove their sharper support.
Reference: Gutleb–Olver, arXiv:1906.03907, Section 3.1, and DLMF 18.37.8.
-/

public section
open Polynomial
namespace MvPolynomial

/-- Entrywise effect of the signed coordinate transport. -/
theorem proriolVolterraCoordinateTransport_apply (N : ℕ)
    (c : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} →₀ ℝ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    proriolVolterraCoordinateTransport N c ⟨d.1 0+d.1 1, ⟨d.1 1, by omega⟩⟩ =
      (-1 : ℝ)^(d.1 0) * c d := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c e hc he => simp [hc, he, mul_add]
  | single e a =>
    rw [proriolVolterraCoordinateTransport, Finsupp.linearCombination_single]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases he : e = d
    · rw [he]
      simp [mul_comm]
    · have hn : (⟨d.1 0+d.1 1, ⟨d.1 1, by omega⟩⟩ : Σ n : ℕ, Fin (n+1)) ≠
          ⟨e.1 0+e.1 1, ⟨e.1 1, by omega⟩⟩ := by
        intro h
        exact he (Subtype.ext (diskIndex_injective h)).symm
      rw [Finsupp.single_eq_of_ne hn, Finsupp.single_eq_of_ne (Ne.symm he)]
      simp

/-- Every extension entry is an explicit finite polynomial moment quotient.
The moment operation is a finite sum of monomial coefficients divided by
positive integers; the norm denominator is strictly positive. -/
theorem proriolExtensionCoefficients_eq_moment (N : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ N)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    proriolExtensionCoefficients N p hp ⟨d.1 0+d.1 1, ⟨d.1 1, by omega⟩⟩ =
      (-1 : ℝ)^(d.1 0) *
        proriolTriangleMoment (triangleExtendY p * proriol 0 0 0 (d.1 0+d.1 1) (d.1 1)) /
        proriolTriangleMoment ((proriol 0 0 0 (d.1 0+d.1 1) (d.1 1))^2) := by
  rw [proriolExtensionCoefficients, proriolVolterraCoordinateTransport_apply,
    proriolDegreeBasis_repr_zero]
  ring

/-- All extension entries as finite coefficient sums with an elementary
normalization factor. No norm integral or basis-coordinate operation remains. -/
theorem proriolExtensionCoefficients_eq_scaled_moment (N : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ N)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N}) :
    proriolExtensionCoefficients N p hp ⟨d.1 0+d.1 1, ⟨d.1 1, by omega⟩⟩ =
      (-1 : ℝ)^(d.1 0) * (2*((d.1 0 : ℝ)+d.1 1+1)*(2*d.1 1+1)) *
        proriolTriangleMoment (triangleExtendY p * proriol 0 0 0 (d.1 0+d.1 1) (d.1 1)) := by
  rw [proriolExtensionCoefficients_eq_moment, proriolTriangleMoment_sq_proriol]
  simp only [div_div_eq_mul_div, div_one]
  ring

end MvPolynomial
