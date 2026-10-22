/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskLift
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Parity
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Cartesian Dunkl–Xu disk polynomials

The Jacobi normalization matches `DunklXuDisk` in
MultivariateOrthogonalPolynomials.jl. The degree block is `n`, with inner indices
`k = 0,...,n`. These polynomials are not orthonormally scaled.

The definition is polynomial everywhere. Its separated square-root formula
is an evaluation identity, valid whenever the first coordinate lies in `(-1,1)`.

References: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*;
https://github.com/JuliaApproximation/MultivariateOrthogonalPolynomials.jl/blob/master/src/rectdisk.jl
-/

@[expose] public section
namespace MvPolynomial

/-- Cartesian Dunkl–Xu polynomials in Jacobi normalization. The degree-indexed
family uses `k ≤ n`; the formula is defined for all natural indices. -/
noncomputable def dunklXuDisk (β : ℝ) (n k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  (Polynomial.jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)).eval₂ C (X 0) *
    diskLift k (Polynomial.jacobi β β k)

/-- The standard separated Jacobi formula holds throughout the open vertical
strip, in particular on the disk interior. -/
theorem eval_dunklXuDisk (β : ℝ) (n k : ℕ) (v : Fin 2 → ℝ)
    (hv : v 0 ^ 2 < 1) :
    eval v (dunklXuDisk β n k) =
      (Polynomial.jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)).eval (v 0) *
        (Real.sqrt (1 - v 0 ^ 2) ^ k *
          (Polynomial.jacobi β β k).eval (v 1 / Real.sqrt (1 - v 0 ^ 2))) := by
  have hs : Real.sqrt (1 - v 0 ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  rw [dunklXuDisk, map_mul, eval_eval₂_C_X,
    eval_diskLift_scaled k _ (Polynomial.natDegree_jacobi_le β β k)
      (Polynomial.coeff_jacobi_symmetric_eq_zero_of_parity β k) v
      (Real.sqrt (1 - v 0 ^ 2)) (v 1 / Real.sqrt (1 - v 0 ^ 2))]
  · rw [Real.sq_sqrt (by linarith)]
  · field_simp

/-- The algebraic construction has total degree at most its outer index. -/
theorem totalDegree_dunklXuDisk_le (β : ℝ) (n k : ℕ) (hkn : k ≤ n) :
    (dunklXuDisk β n k).totalDegree ≤ n := by
  unfold dunklXuDisk
  have h₁ := totalDegree_eval₂_C_X_le
    (Polynomial.jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)) (0 : Fin 2)
  have h₂ := Polynomial.natDegree_jacobi_le (β + k + 1 / 2) (β + k + 1 / 2) (n - k)
  have h₃ := totalDegree_diskLift_le k (Polynomial.jacobi β β k)
  have h₄ := totalDegree_mul
    ((Polynomial.jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)).eval₂ C
      (X 0 : MvPolynomial (Fin 2) ℝ)) (diskLift k (Polynomial.jacobi β β k))
  omega

/-- The constant disk polynomial is one. -/
@[simp] theorem dunklXuDisk_zero_zero (β : ℝ) : dunklXuDisk β 0 0 = 1 := by
  simp [dunklXuDisk, diskLift]

/-- The zero inner index is the symmetric Jacobi polynomial in the first coordinate. -/
theorem dunklXuDisk_zero_inner (β : ℝ) (n : ℕ) :
    dunklXuDisk β n 0 = (Polynomial.jacobi (β + 1 / 2) (β + 1 / 2) n).eval₂ C (X 0) := by
  simp [dunklXuDisk, diskLift]

end MvPolynomial
