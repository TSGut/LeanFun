/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Shifted
public import LeanFun.Mathlib.Algebra.MvPolynomial.ScaledLift
import Mathlib.Tactic.Ring

/-! # Proriol polynomials on the triangle
The division-free definition matches DLMF 18.37.7 on 0<y<x<1:
P_(n-k)^(alpha,beta+gamma+2k+1)(2x-1) x^k P_k^(beta,gamma)(2y/x-1).
It extends polynomially to the whole plane, including the collapsed edge x=0.
-/

@[expose] public section
open Polynomial
namespace MvPolynomial

/-- Proriol triangle polynomials in the standard Jacobi normalization (DLMF 18.37.7). -/
noncomputable def proriol (α β γ : ℝ) (n k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  (shiftedJacobi α (β + γ + 2 * k + 1) (n - k)).eval₂ C (X 0) *
    scaledLift Polynomial.X 1 k (shiftedJacobi β γ k)

/-- The separated polynomial identity is valid even on the collapsed edge. -/
theorem eval_proriol_scaled (α β γ : ℝ) (n k : ℕ) (x z : ℝ) :
    eval (![x, x * z] : Fin 2 → ℝ) (proriol α β γ n k) =
      (shiftedJacobi α (β + γ + 2 * k + 1) (n - k)).eval x * x ^ k *
        (shiftedJacobi β γ k).eval z := by
  rw [proriol, map_mul, eval_eval₂_C_X,
    eval_scaledLift Polynomial.X 1 k (shiftedJacobi β γ k)
      (natDegree_shiftedJacobi_le β γ k) (fun _ _ _ ↦ one_dvd _) _ x z
      (by simp) (by simp)]
  simp [mul_assoc]

/-- Away from x=0, this is exactly the displayed Jacobi formula in DLMF 18.37.7. -/
theorem eval_proriol (α β γ : ℝ) (n k : ℕ) (x y : ℝ) (hx : x ≠ 0) :
    eval (![x, y] : Fin 2 → ℝ) (proriol α β γ n k) =
      (jacobi α (β + γ + 2 * k + 1) (n - k)).eval (2 * x - 1) * x ^ k *
        (jacobi β γ k).eval (2 * (y / x) - 1) := by
  simpa [eval_shiftedJacobi, mul_div_cancel₀ y hx] using
    eval_proriol_scaled α β γ n k x (y / x)

/-- The valid triangular indices belong to the expected total-degree space. -/
theorem totalDegree_proriol_le (α β γ : ℝ) {n k : ℕ} (hk : k ≤ n) :
    (proriol α β γ n k).totalDegree ≤ n := by
  have ho := (totalDegree_eval₂_C_X_le
    (shiftedJacobi α (β + γ + 2 * k + 1) (n - k)) (0 : Fin 2)).trans
      (natDegree_shiftedJacobi_le _ _ _)
  have hi := totalDegree_scaledLift_le (Polynomial.X : ℝ[X]) 1 k
    (shiftedJacobi β γ k) (by simp)
  exact (totalDegree_mul _ _).trans (by omega)

end MvPolynomial
