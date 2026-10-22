/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionGram

/-! # Exact finite polynomial coordinates

Finite expansions with explicit degree bounds provide padded matrix products.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, §3.5.
-/

public section
open MeasureTheory Module
namespace Polynomial.Sequence
variable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ}
    (hP : P.IsOrthogonal μ) (hu : ∀ i, IsUnit (P i).leadingCoeff)
include hμ hpos hP

/-- Finite coordinate multiplication is exact when the intermediate polynomial fits. -/
theorem IsOrthogonal.repr_map_sum (b : Basis ℕ ℝ ℝ[X]) (L : ℝ[X] →ₗ[ℝ] ℝ[X])
    (p : ℝ[X]) (N : ℕ) (hp : p.natDegree < N) (i : ℕ) :
    b.repr (L p) i = ∑ k : Fin N, b.repr (L (P k)) i * (P.basis hu).repr p k := by
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ b.repr (L (P k)) i * (P.basis hu).repr p k) N]
  have he := congrArg (fun p ↦ b.repr (L p) i) (hP.sum_range_repr hμ hpos hu p N hp)
  simpa only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, mul_comm] using he.symm

/-- The finite coefficient dot product is the integral pairing in an orthonormal basis. -/
theorem IsOrthogonal.integralInner_eq_sum_repr
    (hnorm : ∀ n, integralInner μ (hμ.pair (P n) (P n)) = 1)
    (p q : ℝ[X]) (N : ℕ) (hp : p.natDegree < N) :
    integralInner μ (hμ.pair p q) =
      ∑ k : Fin N, (P.basis hu).repr p k * (P.basis hu).repr q k := by
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (P.basis hu).repr p k * (P.basis hu).repr q k) N]
  have he := congrArg (fun p ↦ integralInner μ (hμ.pair p q))
    (hP.sum_range_repr hμ hpos hu p N hp)
  rw [← he, integralInner_sum_left hμ]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integralInner_smul_left (h := hμ.integrable_mul _ _), integralInner_comm μ (P k),
    hP.integralInner_eq_basis_repr_mul hμ hu, hnorm, mul_one]

/-- A bilinear multiplication form is computed by a padded Jacobi section. -/
theorem IsOrthogonal.integralInner_mul_eq_sum_repr
    (hnorm : ∀ n, integralInner μ (hμ.pair (P n) (P n)) = 1)
    (p q u : ℝ[X]) (N : ℕ) (hp : p.natDegree < N) (hq : q.natDegree < N) :
    integralInner μ (hμ.pair p (u*q)) =
      ∑ i : Fin N, ∑ j : Fin N,
        (P.basis hu).repr p i * (P.basis hu).repr (u*P j) i *
          (P.basis hu).repr q j := by
  rw [hP.integralInner_eq_sum_repr hμ hpos hu hnorm p (u*q) N hp]
  apply Finset.sum_congr rfl
  intro i hi
  have he := hP.repr_map_sum hμ hpos hu (P.basis hu) (LinearMap.mulLeft ℝ u) q N hq i
  simp only [LinearMap.mulLeft_apply] at he
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_assoc]

end Polynomial.Sequence
