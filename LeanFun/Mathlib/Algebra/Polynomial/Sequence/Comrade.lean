/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! # Multiplication modulo a polynomial in a degree-graded basis
This is the algebraic comrade-matrix construction; Chebyshev bases give colleague
matrices. Reference: ATAP, Chapter 18; DLMF §3.5(vi).
-/

@[expose] public section
open Module
namespace Polynomial.Sequence
variable {K : Type*} [Field K] (P : Sequence K)

/-- A degree-graded basis has no coordinates above the polynomial's degree. -/
theorem basis_repr_eq_zero_of_degree_lt {p : K[X]} {n j : ℕ}
    (hp : p.degree < n) (hj : n ≤ j) :
    (P.basis P.isUnit_leadingCoeff).repr p j = 0 := by
  have hs : p ∈ Submodule.span K (P '' Set.Iio n) := by
    rw [P.span_degreeLT (fun i _ ↦ P.isUnit_leadingCoeff i)]
    exact mem_degreeLT.mpr hp
  clear hp
  induction hs using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨i, hi, rfl⟩ := hq
    rw [← P.basis_eq_self P.isUnit_leadingCoeff i, Basis.repr_self]
    simp [show i ≠ j by exact ne_of_lt (lt_of_lt_of_le hi hj)]
  | zero => simp
  | add q r _ _ hq hr => simp [hq, hr]
  | smul a q _ hq => simp [hq]

/-- Finite reconstruction below a degree cutoff, without orthogonality hypotheses. -/
theorem sum_fin_repr {p : K[X]} {n : ℕ} (hp : p.degree < n) :
    ∑ i : Fin n, (P.basis P.isUnit_leadingCoeff).repr p i • P i = p := by
  classical
  change (∑ i : Fin n, (fun j : ℕ ↦ (P.basis P.isUnit_leadingCoeff).repr p j • P j) i) = p
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ (P.basis P.isUnit_leadingCoeff).repr p j • P j) n]
  have hs : ((P.basis P.isUnit_leadingCoeff).repr p).support ⊆ Finset.range n := by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hn
    exact Finsupp.mem_support_iff.mp hj
      (P.basis_repr_eq_zero_of_degree_lt hp (by omega))
  have he := (P.basis P.isUnit_leadingCoeff).linearCombination_repr p
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, basis_eq_self] at he
  conv_rhs => rw [← he]
  exact (Finset.sum_subset hs (fun j _ hj ↦ by
    rw [Finsupp.notMem_support_iff.mp hj, zero_smul])).symm

/-- A finite expansion in the first n polynomials has degree below n. -/
theorem degree_sum_fin_lt (n : ℕ) (v : Fin n → K) :
    (∑ i : Fin n, v i • P i).degree < n := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr
  intro i _
  exact lt_of_le_of_lt (degree_smul_le _ _) (by rw [P.degree_eq]; exact WithBot.coe_lt_coe.mpr i.isLt)

/-- The first deg(g) members form a basis of K[X]/(g), for monic g. -/
noncomputable def quotientBasis {g : K[X]} (hg : g.Monic) :
    Basis (Fin g.natDegree) K (AdjoinRoot g) :=
  Basis.ofEquivFun
    { toFun := fun x i ↦ (P.basis P.isUnit_leadingCoeff).repr (AdjoinRoot.modByMonicHom hg x) i
      invFun := fun v ↦ AdjoinRoot.mk g (∑ i, v i • P i)
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro a x; ext i; simp
      left_inv := by
        intro x
        dsimp only
        rw [P.sum_fin_repr (by
          rw [← degree_eq_natDegree hg.ne_zero]
          induction x using AdjoinRoot.induction_on with
          | ih p => exact degree_modByMonic_lt p hg)]
        exact AdjoinRoot.mk_leftInverse hg x
      right_inv := by
        intro v
        funext i
        dsimp only
        rw [AdjoinRoot.modByMonicHom_mk,
          (modByMonic_eq_self_iff hg).mpr (by
            rw [degree_eq_natDegree hg.ne_zero]
            exact P.degree_sum_fin_lt _ v)]
        simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
        have hb (j : Fin g.natDegree) :
            (P.basis P.isUnit_leadingCoeff).repr (P j) = Finsupp.single (j : ℕ) 1 := by
          rw [← P.basis_eq_self P.isUnit_leadingCoeff j, Basis.repr_self]
        simp only [hb, Finsupp.single_apply, ← Fin.ext_iff, mul_ite, mul_one, mul_zero]
        simp }

/-- The quotient basis is the image of the original degree-graded sequence. -/
@[simp] theorem quotientBasis_apply {g : K[X]} (hg : g.Monic) (i : Fin g.natDegree) :
    P.quotientBasis hg i = AdjoinRoot.mk g (P i) := by
  simp only [quotientBasis, Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk, Pi.single_apply]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Coordinates are obtained by taking the polynomial remainder first. -/
@[simp] theorem quotientBasis_repr {g : K[X]} (hg : g.Monic)
    (x : AdjoinRoot g) (i : Fin g.natDegree) :
    (P.quotientBasis hg).repr x i =
      (P.basis P.isUnit_leadingCoeff).repr (AdjoinRoot.modByMonicHom hg x) i := rfl

/-- The comrade matrix has columns given by multiplication by X modulo g. -/
noncomputable def comradeMatrix {g : K[X]} (hg : g.Monic) :
    Matrix (Fin g.natDegree) (Fin g.natDegree) K :=
  Algebra.leftMulMatrix (P.quotientBasis hg) (AdjoinRoot.root g)

/-- Entries use the existing polynomial coordinates and the monic remainder. -/
theorem comradeMatrix_apply {g : K[X]} (hg : g.Monic) (i j : Fin g.natDegree) :
    P.comradeMatrix hg i j =
      (P.basis P.isUnit_leadingCoeff).repr ((X * P j) %ₘ g) i := by
  rw [comradeMatrix, Algebra.leftMulMatrix_eq_repr_mul, quotientBasis_apply,
    ← AdjoinRoot.mk_X, ← map_mul, quotientBasis_repr, AdjoinRoot.modByMonicHom_mk]

/-- The characteristic polynomial is exactly the monic input polynomial. -/
theorem charpoly_comradeMatrix {g : K[X]} (hg : g.Monic) :
    (P.comradeMatrix hg).charpoly = g := by
  let := (AdjoinRoot.powerBasis' hg).finite
  rw [comradeMatrix, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix,
    ← LinearMap.charpoly_toMatrix _ (AdjoinRoot.powerBasis hg.ne_zero).basis,
    ← Algebra.leftMulMatrix_apply]
  exact (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hg.ne_zero)).trans
    (AdjoinRoot.minpoly_powerBasis_gen_of_monic hg)

/-- The matrix spectrum is precisely the roots of the defining polynomial. -/
theorem mem_spectrum_comradeMatrix_iff {g : K[X]} (hg : g.Monic) (x : K) :
    x ∈ spectrum K (P.comradeMatrix hg) ↔ g.IsRoot x := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, P.charpoly_comradeMatrix hg]

/-- Explicit rank-one correction to the leading multiplication section.
Only the top-degree coefficient of X times a basis member is removed. -/
theorem comradeMatrix_rank_one_entry {g : K[X]} (hg : g.Monic)
    (i j : Fin g.natDegree) :
    P.comradeMatrix hg i j =
      (P.basis P.isUnit_leadingCoeff).repr (X * P j) i -
        (X * P j).coeff g.natDegree * (P.basis P.isUnit_leadingCoeff).repr g i := by
  have hq : ((X * P j) /ₘ g).natDegree = 0 := by
    rw [natDegree_divByMonic _ hg, natDegree_X_mul (P.ne_zero j), P.natDegree_eq]
    omega
  have heq := congrArg (fun q : K[X] ↦ g * q) (eq_C_of_natDegree_eq_zero hq)
  have hc := congrArg (fun p : K[X] ↦ p.coeff g.natDegree) (modByMonic_add_div (X * P j) g)
  rw [heq, coeff_add, coeff_mul_C, hg.coeff_natDegree,
    coeff_eq_zero_of_degree_lt (by
      rw [← degree_eq_natDegree hg.ne_zero]
      exact degree_modByMonic_lt _ hg), zero_add, one_mul] at hc
  rw [P.comradeMatrix_apply, modByMonic_eq_sub_mul_div, heq, hc, mul_comm g,
    ← smul_eq_C_mul, map_sub, map_smul]
  rfl

/-- Every column except the last agrees with ordinary multiplication by X. -/
theorem comradeMatrix_apply_of_lt {g : K[X]} (hg : g.Monic)
    (i j : Fin g.natDegree) (hj : (j : ℕ) + 1 < g.natDegree) :
    P.comradeMatrix hg i j = (P.basis P.isUnit_leadingCoeff).repr (X * P j) i := by
  rw [P.comradeMatrix_rank_one_entry,
    coeff_eq_zero_of_natDegree_lt (by
      rw [natDegree_X_mul (P.ne_zero j), P.natDegree_eq]
      exact hj), zero_mul, sub_zero]

end Polynomial.Sequence
