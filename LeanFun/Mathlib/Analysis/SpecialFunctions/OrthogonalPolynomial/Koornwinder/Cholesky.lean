/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Koornwinder.GramFactor
public import LeanFun.Mathlib.LinearAlgebra.Matrix.CholeskyLU

/-!
# Positive Cholesky factors on separated sections

The enumeration and triangular support are explicit. Compatible finite spans,
normalization and positivity identify the mixed pairings with Cholesky, and
with the zero pattern of exact unpivoted LU.
Reference: Gutleb–Olver–Slevinsky, Lemma 2.8.
-/

public section
open MeasureTheory Polynomial Module Matrix
namespace MvPolynomial.KoornwinderSystem
variable {D : Set ℝ}
variable {a : ℝ[X]} {ρ : D → ℝ} {μ : Measure D} {ν : Measure ℝ} {μ' : Measure D} {ν' : Measure ℝ}
    (S : KoornwinderSystem a ρ μ ν) (T : KoornwinderSystem a ρ μ' ν')
    (hμ' : Polynomial.HasFiniteMoments (Measure.map Subtype.val μ')) (hν' : Polynomial.HasFiniteMoments ν')
    (hρ : Continuous ρ) (habs : μ' ≪ μ) (ha : ∀ᵐ x ∂μ', ρ x^2 = a.eval (x : ℝ))
    (N M : ℕ) (e : Fin M ≃ KoornwinderIndex N)
    (hspan : ∀ i : KoornwinderIndex N, S.polynomial i.1 i.2 ∈ T.sectionSpan N)
    (hupper : ∀ i j : Fin M, j < i →
      S.connectionEntry T (e j).1 (e j).2 (e i).1 (e i).2 = 0)

/-- Nonnegative separated offsets give scalar triangularity in degree/inner order. -/
theorem connectionEntry_upperTriangular_of_support
    (horder : ∀ i j : Fin M, i < j →
      (e i).1.val < (e j).1.val ∨
        (e i).1.val = (e j).1.val ∧ (e i).2.val < (e j).2.val)
    (hzero : ∀ n k m j, k ≤ n → j ≤ m → n < m ∨ k < j →
      S.connectionEntry T n k m j = 0) :
    (Matrix.of (fun i j : Fin M =>
      S.connectionEntry T (e j).1 (e j).2 (e i).1 (e i).2)).IsUpperTriangular := by
  intro i j hij
  apply hzero _ _ _ _ (Nat.le_of_lt_succ (e j).2.isLt) (Nat.le_of_lt_succ (e i).2.isLt)
  rcases horder j i hij with h | h
  · exact Or.inl h
  · exact Or.inr h.2

include hμ' hν' hρ ha hspan

/-- Reindexing the normalized connection preserves the exact Gram factorization. -/
theorem connectionEntry_gram_reindex :
    Matrix.of (fun i j : Fin M => integralInner (koornwinderMeasure ρ μ' ν') (IntegrablePair.of (koornwinderMeasure ρ μ' ν') (S.polynomial (e i).1 (e i).2) (S.polynomial (e j).1 (e j).2))) =
      (Matrix.of (fun i j : Fin M =>
        S.connectionEntry T (e j).1 (e j).2 (e i).1 (e i).2)).transpose *
      Matrix.of (fun i j : Fin M => S.connectionEntry T (e j).1 (e j).2 (e i).1 (e i).2) := by
  have he := congrArg (fun A => A.submatrix e e) (S.connectionEntry_gram T hμ' hν' hρ ha N hspan)
  rw [← Matrix.submatrix_mul_equiv _ _ e e e] at he
  exact he

include habs hupper

/-- Every other positive upper triangular Gram factor equals the separated connection. -/
theorem connectionEntry_eq_of_gram_factor (R : Matrix (Fin M) (Fin M) ℝ)
    (hR : R.IsUpperTriangular) (hRp : ∀ i, 0 < R i i)
    (hg : Matrix.of (fun i j : Fin M => integralInner (koornwinderMeasure ρ μ' ν') (IntegrablePair.of (koornwinderMeasure ρ μ' ν') (S.polynomial (e i).1 (e i).2) (S.polynomial (e j).1 (e j).2))) = R.transpose*R) :
    Matrix.of (fun i j : Fin M => S.connectionEntry T (e j).1 (e j).2 (e i).1 (e i).2) = R := by
  exact Matrix.eq_of_pos_upperTriangular_gram_eq hupper hR
    (fun i => S.connectionEntry_diag_pos T hμ' hν' hρ habs ha _ _) hRp
    ((S.connectionEntry_gram_reindex T hμ' hν' hρ ha N M e hspan).symm.trans hg)

/-- Exact unit-lower LU has the same upper-factor zeros as the separated connection. -/
theorem connectionEntry_lu_support (L U : Matrix (Fin M) (Fin M) ℝ)
    (hL : L.transpose.IsUpperTriangular) (hd : ∀ i, L i i = 1) (hU : U.IsUpperTriangular)
    (hLU : Matrix.of (fun i j : Fin M => integralInner (koornwinderMeasure ρ μ' ν') (IntegrablePair.of (koornwinderMeasure ρ μ' ν') (S.polynomial (e i).1 (e i).2) (S.polynomial (e j).1 (e j).2))) = L*U) :
    ∀ i j, U i j = 0 ↔ S.connectionEntry T (e j).1 (e j).2 (e i).1 (e i).2 = 0 := by
  let C := Matrix.of (fun i j : Fin M => S.connectionEntry T (e j).1 (e j).2 (e i).1 (e i).2)
  have ht : C.IsUpperTriangular := hupper
  have he := Matrix.upper_eq_of_diagonal_gram_factor _ C L U (fun _ => 1)
    (fun _ => one_ne_zero) ht
    (fun i => (S.connectionEntry_diag_pos T hμ' hν' hρ habs ha _ _).ne')
    (by simpa only [C, inv_one, diagonal_one, one_mul, mul_one] using
      (S.connectionEntry_gram_reindex T hμ' hν' hρ ha N M e hspan).symm)
    hL hd hU hLU
  exact he.2

end MvPolynomial.KoornwinderSystem
