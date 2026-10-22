/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionSupport
public import LeanFun.Mathlib.Analysis.InnerProductSpace.GramSchmidtFactor

/-!
# Leading sections of univariate polynomial connections

Every leading connection section into a positive-leading orthonormal sequence
is the unique positive upper triangular factor of the source Gram section.
Reference: Gutleb–Olver–Slevinsky, Lemma 2.8 (Gautschi's measure conversion).
-/

public section
open MeasureTheory Module
namespace Polynomial.Sequence
variable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {Q : Sequence ℝ} (hQ : Q.IsOrthogonal μ)
    (hu : ∀ i, IsUnit (Q i).leadingCoeff)
include hμ hpos hQ

/-- Every polynomial of degree below N expands in the first N basis vectors. -/
theorem IsOrthogonal.sum_range_repr (p : ℝ[X]) (N : ℕ) (hp : p.natDegree < N) :
    ∑ k ∈ Finset.range N, (Q.basis hu).repr p k • Q k = p := by
  classical
  have hs : ((Q.basis hu).repr p).support ⊆ Finset.range N := by
    intro k hk
    apply Finset.mem_range.mpr
    by_contra hn
    exact Finsupp.mem_support_iff.mp hk
      (hQ.basis_repr_eq_zero_of_natDegree_lt hμ hpos hu (lt_of_lt_of_le hp (by omega)))
  have he := (Q.basis hu).linearCombination_repr p
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, basis_eq_self] at he
  conv_rhs => rw [← he]
  symm
  apply Finset.sum_subset hs
  intro k _ hk
  rw [Finsupp.notMem_support_iff.mp hk, zero_smul]

/-- Coordinates of a degree-indexed source form an upper triangular leading section. -/
theorem IsOrthogonal.connection_upperTriangular (P : Sequence ℝ) (N : ℕ) :
    (Matrix.of (fun i j : Fin N => (Q.basis hu).repr (P j) i)).IsUpperTriangular := by
  intro i j hij
  exact hQ.basis_repr_eq_zero_of_natDegree_lt hμ hpos hu (by simpa using hij)

/-- Positive leading coefficients give a positive diagonal connection. -/
theorem IsOrthogonal.connection_diag_pos (P : Sequence ℝ)
    (hP : ∀ n, 0 < (P n).leadingCoeff) (hQl : ∀ n, 0 < (Q n).leadingCoeff) (n : ℕ) :
    0 < (Q.basis hu).repr (P n) n := by
  rw [hQ.basis_repr_eq_integralInner_div hμ hpos hu]
  have hn : 0 < integralInner μ (IntegrablePair.of μ (Q n) (Q n)) := by
    rw [integralInner_self]
    exact hpos _ (Q.ne_zero n)
  exact div_pos (hQ.integralInner_pos_of_leadingCoeff_pos hμ
    (P.natDegree_eq n) (hP n) (hQl n) hn) hn

/-- The leading connection into an orthonormal sequence factors the Gram section. -/
theorem IsOrthogonal.connection_gram (P : Sequence ℝ)
    (hnorm : ∀ n, integralInner μ (IntegrablePair.of μ (Q n) (Q n)) = 1) (N : ℕ) :
    Matrix.of (fun i j : Fin N => integralInner μ (IntegrablePair.of μ (P i) (P j))) =
      (Matrix.of (fun i j : Fin N => (Q.basis hu).repr (P j) i)).transpose *
        (Matrix.of (fun i j : Fin N => (Q.basis hu).repr (P j) i)) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (Q.basis hu).repr (P i) k * (Q.basis hu).repr (P j) k) N]
  have he := hQ.sum_range_repr hμ hpos hu (P i) N (by simp)
  have he' := congrArg (fun p : ℝ[X] => integralInner μ (hμ.pair p (P j))) he
  rw [← he']
  rw [integralInner_sum_left hμ]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integralInner_smul_left (h := hμ.integrable_mul _ _), integralInner_comm μ (Q k),
    hQ.integralInner_eq_basis_repr_mul hμ hu, hnorm, mul_one]

/-- Leading connection sections compose exactly, with no additional padding. -/
theorem IsOrthogonal.connection_comp (P S : Sequence ℝ)
    (hS : ∀ i, IsUnit (S i).leadingCoeff) (N : ℕ) :
    Matrix.of (fun i j : Fin N => (S.basis hS).repr (P j) i) =
      Matrix.of (fun i j : Fin N => (S.basis hS).repr (Q j) i) *
        Matrix.of (fun i j : Fin N => (Q.basis hu).repr (P j) i) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (S.basis hS).repr (Q k) i * (Q.basis hu).repr (P j) k) N]
  have he := congrArg (fun p => (S.basis hS).repr p i)
    (hQ.sum_range_repr hμ hpos hu (P j) N (by simp))
  simpa only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, mul_comm] using he.symm

/-- The positive-leading connection is the unique positive triangular Gram factor. -/
theorem IsOrthogonal.connection_eq_of_gram (P : Sequence ℝ)
    (hPl : ∀ n, 0 < (P n).leadingCoeff) (hQl : ∀ n, 0 < (Q n).leadingCoeff)
    (hnorm : ∀ n, integralInner μ (IntegrablePair.of μ (Q n) (Q n)) = 1) (N : ℕ)
    (R : Matrix (Fin N) (Fin N) ℝ) (hR : R.IsUpperTriangular)
    (hRp : ∀ i, 0 < R i i)
    (hg : Matrix.of (fun i j : Fin N => integralInner μ (IntegrablePair.of μ (P i) (P j))) = R.transpose * R) :
    Matrix.of (fun i j : Fin N => (Q.basis hu).repr (P j) i) = R :=
  Matrix.eq_of_pos_upperTriangular_gram_eq
    (hQ.connection_upperTriangular hμ hpos hu P N) hR
    (fun i => hQ.connection_diag_pos hμ hpos hu P hPl hQl i) hRp
    ((hQ.connection_gram hμ hpos hu P hnorm N).symm.trans hg)

end Polynomial.Sequence
