/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Polynomial.Sequence.Comrade

/-! # Leading multiplication sections and characteristic polynomials
For an orthogonal sequence this is the finite Jacobi matrix in the original
normalization. Reference: DLMF §3.5(vi); ATAP, Chapter 18.
-/

@[expose] public section
namespace Polynomial.Sequence
variable {K : Type*} [Field K] (P : Sequence K)

/-- The leading section of multiplication by X, with basis images as columns. -/
noncomputable def jacobiMatrix (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j ↦ (P.basis P.isUnit_leadingCoeff).repr (X * P j) i

/-- Taking the remainder modulo the next sequence polynomial preserves the
lower coordinates of multiplication by X. -/
theorem repr_X_mul_mod_next (n : ℕ) (i j : Fin n) :
    (P.basis P.isUnit_leadingCoeff).repr
      ((X * P j) %ₘ (P n * C (P n).leadingCoeff⁻¹)) i = P.jacobiMatrix n i j := by
  let g := P n * C (P n).leadingCoeff⁻¹
  have hg : g.Monic := monic_mul_leadingCoeff_inv (P.ne_zero n)
  have hd : g.natDegree = n := by
    simp [g, natDegree_mul, leadingCoeff_ne_zero.mpr (P.ne_zero n)]
  have hq : ((X * P j) /ₘ g).natDegree = 0 := by
    rw [natDegree_divByMonic _ hg, hd, natDegree_X_mul (P.ne_zero j), P.natDegree_eq]
    omega
  have he : g * ((X * P j) /ₘ g) =
      ((P n).leadingCoeff⁻¹ * (((X * P j) /ₘ g).coeff 0)) • P n := by
    rw [eq_C_of_natDegree_eq_zero hq]
    simp only [g, smul_eq_C_mul, map_mul, coeff_C_zero]
    ring
  change (P.basis P.isUnit_leadingCoeff).repr ((X * P j) %ₘ g) i = _
  rw [modByMonic_eq_sub_mul_div, he, map_sub, map_smul]
  have hb : (P.basis P.isUnit_leadingCoeff).repr (P n) = Finsupp.single n 1 := by
    rw [← P.basis_eq_self P.isUnit_leadingCoeff n, Module.Basis.repr_self]
  simp [hb, ne_of_gt i.isLt, jacobiMatrix]

/-- The characteristic polynomial is the next sequence member made monic.
Orthogonality is not needed for this algebraic identity. -/
theorem charpoly_jacobiMatrix (n : ℕ) :
    (P.jacobiMatrix n).charpoly = P n * C (P n).leadingCoeff⁻¹ := by
  let g := P n * C (P n).leadingCoeff⁻¹
  have hg : g.Monic := monic_mul_leadingCoeff_inv (P.ne_zero n)
  have hd : g.natDegree = n := by
    simp [g, natDegree_mul, leadingCoeff_ne_zero.mpr (P.ne_zero n)]
  have he : Matrix.reindex (finCongr hd) (finCongr hd) (P.comradeMatrix hg) =
      P.jacobiMatrix n := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [P.comradeMatrix_apply]
    exact P.repr_X_mul_mod_next n i j
  rw [← he, Matrix.charpoly_reindex, P.charpoly_comradeMatrix hg]

/-- The finite multiplication section has precisely the next polynomial's roots
as its spectrum, with no requirement that those roots lie in the base field. -/
theorem mem_spectrum_jacobiMatrix_iff (n : ℕ) (x : K) :
    x ∈ spectrum K (P.jacobiMatrix n) ↔ (P n).IsRoot x := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, P.charpoly_jacobiMatrix]
  simp [IsRoot, eval_mul, leadingCoeff_ne_zero.mpr (P.ne_zero n)]

/-- Evaluation at a root gives a left eigenvector in the original coordinates. -/
theorem sum_jacobiMatrix_mul_eval {n : ℕ} {x : K} (hx : (P n).eval x = 0)
    (i : Fin n) :
    ∑ j : Fin n, P.jacobiMatrix n j i * (P j).eval x = x * (P i).eval x := by
  have hd : (X * P i).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_X, P.degree_eq]
    exact_mod_cast (show 1 + (i : ℕ) < n + 1 by omega)
  have he := congrArg (fun p : K[X] ↦ p.eval x) (P.sum_fin_repr hd)
  simp only [eval_finsetSum, eval_smul, smul_eq_mul] at he
  rw [Fin.sum_univ_castSucc] at he
  simpa only [Fin.val_castSucc, Fin.val_last, hx, mul_zero, add_zero, eval_mul,
    eval_X, jacobiMatrix] using he

end Polynomial.Sequence
