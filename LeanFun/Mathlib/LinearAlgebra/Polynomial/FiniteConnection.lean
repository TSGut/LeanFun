/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Finite polynomial connection formulas

Cramer's rule gives a denominator-cleared expansion, even over rings and at
singular specialisations. Divided coefficients require a nonzero determinant.
References: Cramer's rule; DLMF 18.18(iv) for classical polynomial connections.
-/

@[expose] public section
namespace Polynomial
variable {R : Type*} [CommRing R] {N : ℕ}

/-- The finite monomial coefficient matrix of a polynomial family. -/
def connectionMatrix (p : Fin N → R[X]) : Matrix (Fin N) (Fin N) R :=
  Matrix.of (fun i j ↦ (p j).coeff i)

/-- Cramer's numerator for the coefficient of each member of a finite family. -/
noncomputable def connectionNumerator (p : Fin N → R[X]) (q : R[X]) : Fin N → R :=
  Matrix.cramer (connectionMatrix p) (fun i ↦ q.coeff i)

/-- Each connection numerator is the determinant with one coefficient column
replaced by that of the polynomial to expand (Cramer's rule). -/
theorem connectionNumerator_eq_det (p : Fin N → R[X]) (q : R[X]) (j : Fin N) :
    connectionNumerator p q j =
      (Matrix.updateCol (connectionMatrix p) j (fun i ↦ q.coeff i)).det := rfl

/-- The determinant of a degree-indexed family's coefficient matrix is the
product of its top coefficients; no nonvanishing assumption is needed. -/
theorem det_connectionMatrix (p : Fin N → R[X]) (hp : ∀ j, (p j).natDegree ≤ j) :
    (connectionMatrix p).det = ∏ j : Fin N, (p j).coeff j :=
  Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_isUpperTriangular p hp)

/-- The universal cleared finite connection formula (Cramer's rule).
Both the family members and the polynomial have degree less than the matrix size. -/
theorem det_smul_eq_sum_connectionNumerator (p : Fin N → R[X]) (q : R[X])
    (hp : ∀ j, (p j).degree < N) (hq : q.degree < N) :
    (connectionMatrix p).det • q = ∑ j : Fin N, connectionNumerator p q j • p j := by
  ext k
  simp only [coeff_smul, finsetSum_coeff, smul_eq_mul]
  by_cases hk : k < N
  · have h := congrFun (Matrix.mulVec_cramer (connectionMatrix p) (fun i ↦ q.coeff i))
      (⟨k, hk⟩ : Fin N)
    simpa only [Matrix.mulVec, dotProduct, connectionMatrix, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul, connectionNumerator, mul_comm] using h.symm
  · have hqk : q.coeff k = 0 := coeff_eq_zero_of_degree_lt
      (hq.trans_le (Nat.cast_le.mpr (Nat.le_of_not_gt hk)))
    rw [hqk, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_eq_zero_of_degree_lt ((hp j).trans_le (Nat.cast_le.mpr (Nat.le_of_not_gt hk))),
      mul_zero]

section Field
variable {K : Type*} [Field K]

/-- A finite polynomial family with a nonsingular coefficient matrix. -/
structure FiniteConnectionInput (p : Fin N → K[X]) : Prop where
  nonsingular : (connectionMatrix p).det ≠ 0

/-- Divided finite connection coefficients, meaningful when the matrix is nonsingular. -/
noncomputable def finiteConnectionCoefficient (p : Fin N → K[X]) (q : K[X]) (j : Fin N) (_d : FiniteConnectionInput p) : K :=
  connectionNumerator p q j / (connectionMatrix p).det

/-- Multiplication by the nonzero determinant recovers Cramer's numerator. -/
theorem finiteConnectionCoefficient_mul_det (p : Fin N → K[X]) (q : K[X])
    (j : Fin N) (d : FiniteConnectionInput p) :
    finiteConnectionCoefficient p q j d * (connectionMatrix p).det = connectionNumerator p q j :=
  div_mul_cancel₀ _ d.nonsingular

/-- Dividing the universal identity yields the finite polynomial expansion. -/
theorem eq_sum_finiteConnectionCoefficient (p : Fin N → K[X]) (q : K[X])
    (hp : ∀ j, (p j).degree < N) (hq : q.degree < N)
    (hd : (connectionMatrix p).det ≠ 0) :
    q = ∑ j : Fin N, finiteConnectionCoefficient p q j ⟨hd⟩ • p j := by
  have h := congrArg (fun r : K[X] ↦ (connectionMatrix p).det⁻¹ • r)
    (det_smul_eq_sum_connectionNumerator p q hp hq)
  simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul, Finset.smul_sum,
    finiteConnectionCoefficient, div_eq_mul_inv, mul_comm] using h

end Field
end Polynomial
