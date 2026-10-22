/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Coordinates
public import Mathlib.Algebra.Polynomial.Sequence

/-!
# Cartesian polynomial products on a disk

This construction accepts arbitrary univariate factors. Parity of the inner
factor makes the square-root coordinate formula a genuine polynomial.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

@[expose] public section
open Polynomial Set
namespace MvPolynomial

/-- The polynomial Cartesian product of an outer factor and a parity-lifted inner factor. -/
noncomputable def cartesianDiskPolynomial (p q : ℝ[X]) (k : ℕ) :
    MvPolynomial (Fin 2) ℝ := p.eval₂ C (X 0) * diskLift k q

/-- The Cartesian product has degree bounded by outer degree plus lift degree. -/
theorem totalDegree_cartesianDiskPolynomial_le (p q : ℝ[X]) (k : ℕ) :
    (cartesianDiskPolynomial p q k).totalDegree ≤ p.natDegree + k :=
  (totalDegree_mul _ _).trans
    (Nat.add_le_add (totalDegree_eval₂_C_X_le p 0) (totalDegree_diskLift_le k q))

/-- The square-root formula holds on closed vertical slices, including their endpoints. -/
theorem eval_cartesianDiskPolynomial (p q : ℝ[X]) (k : ℕ)
    (hq : q.natDegree ≤ k) (hpar : ∀ j, j % 2 ≠ k % 2 → q.coeff j = 0)
    (x z : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (x,z)) (cartesianDiskPolynomial p q k) =
      p.eval x * Real.sqrt (1-x^2)^k * q.eval z := by
  have hs : 0 ≤ 1-x^2 := by nlinarith [hx.1,hx.2]
  rw [cartesianDiskPolynomial, map_mul, eval_eval₂_C_X,
    eval_diskLift_scaled k q hq hpar _ (Real.sqrt (1-x^2)) z]
  · simp [ mul_assoc]
  · simpa [] using (Real.sq_sqrt hs).symm
  · simp []

end MvPolynomial
