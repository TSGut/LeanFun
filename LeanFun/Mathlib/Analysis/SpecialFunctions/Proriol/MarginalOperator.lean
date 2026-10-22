/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Marginal
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Polynomial triangle marginal operators

The marginal is a linear map on polynomial kernels. Its action on finite
Proriol expansions is an exact coefficient selector, with the endpoint factor
retained. Reference: Gutleb–Olver, arXiv:1906.03907, Section 3.1.
-/

@[expose] public noncomputable section
open MeasureTheory Polynomial
namespace MvPolynomial

/-- Polynomial kernels are integrable on every finite vertical interval. -/
theorem intervalIntegrable_eval_vertical (p : MvPolynomial (Fin 2) ℝ) (x a b : ℝ) :
    IntervalIntegrable (fun y ↦ eval (![x,y] : Fin 2 → ℝ) p) volume a b :=
  (p.continuous_eval.comp (by fun_prop)).intervalIntegrable a b

/-- The unweighted triangle marginal, with upper endpoint `1-x`.
Its domain is polynomial kernels, so additivity needs no integrability assumptions. -/
def triangleMarginal : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] (ℝ → ℝ) where
  toFun p x := ∫ y in (0 : ℝ)..(1-x), eval (![x,y] : Fin 2 → ℝ) p
  map_add' p q := by
    funext x
    simp only [map_add, Pi.add_apply]
    exact intervalIntegral.integral_add
      (intervalIntegrable_eval_vertical p x 0 (1-x))
      (intervalIntegrable_eval_vertical q x 0 (1-x))
  map_smul' c p := by
    funext x
    simp [smul_eval, intervalIntegral.integral_const_mul]

/-- Reflecting only the first coordinate transports the DLMF triangle to the
simplex used for Volterra operators. -/
def triangleReflect : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  aeval ![1-X 0, X 1]

/-- Pointwise action of first-coordinate reflection. -/
theorem eval_triangleReflect (p : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    eval (![x,y] : Fin 2 → ℝ) (triangleReflect p) =
      eval (![1-x,y] : Fin 2 → ℝ) p := by
  simp only [triangleReflect, aeval_def, algebraMap_eq, eval_eval₂]
  congr 1
  · ext c; simp
  · funext i
    fin_cases i <;> simp

/-- Marginal entries of the reflected, sign-normalized Proriol modes. -/
theorem triangleMarginal_proriol (n k : ℕ) (x : ℝ) :
    triangleMarginal ((-1 : ℝ)^(n-k) • triangleReflect (proriol 0 0 0 n k)) x =
      if k = 0 then (1-x) * (shiftedJacobi 1 0 n).eval x else 0 := by
  change (∫ y in (0 : ℝ)..(1-x), _) = _
  simp only [smul_eval, eval_triangleReflect]
  exact integral_proriol_reflected_normalized n k x

/-- Exact coefficient selection for every finite triangular expansion.
Only inner degree zero contributes; the factor `1-x` is not absorbed into the
coefficient normalization (Gutleb's thesis, equation (2.7)). -/
theorem triangleMarginal_sum_proriol (N : ℕ) (c : ℕ → ℕ → ℝ) (x : ℝ) :
    triangleMarginal (∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n+1),
      c n k • ((-1 : ℝ)^(n-k) • triangleReflect (proriol 0 0 0 n k))) x =
      (1-x) * ∑ n ∈ Finset.range N, c n 0 * (shiftedJacobi 1 0 n).eval x := by
  have hc (n k : ℕ) :
      triangleMarginal (c n k •
        ((-1 : ℝ)^(n-k) • triangleReflect (proriol 0 0 0 n k))) x =
        c n k * (if k = 0 then (1-x) * (shiftedJacobi 1 0 n).eval x else 0) := by
    rw [map_smul, Pi.smul_apply, smul_eq_mul, triangleMarginal_proriol]
  simp only [map_sum, Finset.sum_apply, hc]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.succ_pos, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end MvPolynomial
