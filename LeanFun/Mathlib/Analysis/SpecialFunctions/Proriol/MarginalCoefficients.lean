/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.MarginalOperator
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Proriol marginal coefficient operator

Finitely supported triangular coefficients give an exact polynomial output.
The marginal coefficient matrix selects inner degree zero. The endpoint factor
is a separate multiplication operator. Reference: Gutleb–Olver,
arXiv:1906.03907, Section 3.1; Gutleb's thesis, equation (2.7).
-/

@[expose] public noncomputable section
namespace MvPolynomial
open Polynomial

/-- Synthesis in the reflected and sign-normalized Proriol basis. -/
def proriolVolterraSynthesis : ((Σ n : ℕ, Fin (n+1)) →₀ ℝ) →ₗ[ℝ]
    MvPolynomial (Fin 2) ℝ :=
  Finsupp.linearCombination ℝ (fun i ↦
    (-1 : ℝ)^(i.1-i.2.val) • triangleReflect (proriol 0 0 0 i.1 i.2))

/-- The sparse marginal coefficient operator, before multiplication by `1-x`. -/
def proriolMarginalCoefficients : ((Σ n : ℕ, Fin (n+1)) →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun i ↦
    if i.2 = 0 then Finsupp.single i.1 1 else 0)

/-- Each column has at most one nonzero, in its own total degree. -/
theorem proriolMarginalCoefficients_single (i : Σ n : ℕ, Fin (n+1)) (a : ℝ) :
    proriolMarginalCoefficients (Finsupp.single i a) =
      if i.2 = 0 then Finsupp.single i.1 a else 0 := by
  classical
  simp [proriolMarginalCoefficients, Finsupp.linearCombination_single, smul_ite]

/-- Exact entries of the marginal matrix on the valid triangular index set. -/
theorem proriolMarginalCoefficients_entry (n : ℕ) (i : Σ n : ℕ, Fin (n+1)) :
    proriolMarginalCoefficients (Finsupp.single i 1) n =
      if i.2 = 0 ∧ i.1 = n then 1 else 0 := by
  classical
  rw [proriolMarginalCoefficients_single]
  split_ifs <;> simp_all

/-- The marginal polynomial retains the explicit endpoint factor. -/
def proriolMarginalPolynomial : ((Σ n : ℕ, Fin (n+1)) →₀ ℝ) →ₗ[ℝ] ℝ[X] :=
  (LinearMap.mulLeft ℝ (1-Polynomial.X)).comp
    ((Finsupp.linearCombination ℝ (shiftedJacobi 1 0)).comp proriolMarginalCoefficients)

/-- Polynomial coefficient assembly agrees exactly with analytic marginal
integration on every finite coefficient vector. -/
theorem eval_proriolMarginalPolynomial (c : (Σ n : ℕ, Fin (n+1)) →₀ ℝ) (x : ℝ) :
    (proriolMarginalPolynomial c).eval x = triangleMarginal (proriolVolterraSynthesis c) x := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single i a =>
    have hm : triangleMarginal (proriolVolterraSynthesis (Finsupp.single i a)) x =
        a * (if i.2.val = 0 then (1-x) * (shiftedJacobi 1 0 i.1).eval x else 0) := by
      rw [proriolVolterraSynthesis, Finsupp.linearCombination_single,
        map_smul, Pi.smul_apply, smul_eq_mul, triangleMarginal_proriol]
    rw [hm]
    simp only [proriolMarginalPolynomial, LinearMap.comp_apply,
      proriolMarginalCoefficients_single, LinearMap.mulLeft_apply]
    by_cases hi : i.2 = 0
    · simp [hi, Finsupp.linearCombination_single, Polynomial.smul_eq_C_mul]
      ring
    · have hz : i.2.val ≠ 0 := fun h ↦ hi (Fin.ext h)
      simp [hi, hz]

end MvPolynomial
