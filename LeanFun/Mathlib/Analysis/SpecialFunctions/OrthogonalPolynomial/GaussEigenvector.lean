/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Quadrature
public import LeanFun.Mathlib.Algebra.Polynomial.Sequence.Comrade

/-! # Normalized Gaussian evaluation vectors
The normalization and first-component weight formula follow from quadrature
exactness. Reference: DLMF §3.5(vi), Golub--Welsch.
-/

@[expose] public section
open MeasureTheory
namespace Polynomial.Sequence
variable {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)

include hμ hpos hP

/-- Coordinates of a Gaussian cardinal polynomial, from quadrature exactness. -/
theorem IsOrthogonal.gauss_lagrange_repr {n : ℕ} {x : ℝ}
    (hx : x ∈ (P n).roots.toFinset) (i : Fin n) :
    (P.basis P.isUnit_leadingCoeff).repr (Lagrange.classicalBasis (P n).roots.toFinset id x (Lagrange.BasisInput.id _ _)) i =
      P.gaussWeight μ n x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) * (P i).eval x / P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _) := by
  classical
  let l := Lagrange.basis (P n).roots.toFinset id x
  have hl : l ≠ 0 := Lagrange.basis_ne_zero (fun _ _ _ _ h ↦ h) hx
  have hd : l.natDegree = n - 1 := by
    simpa [l, hP.card_gaussNodes hμ hpos] using
      Lagrange.natDegree_basis (v := id) (fun _ _ _ _ h ↦ h) hx
  have hdeg : (l * P i).degree < (2 * n : ℕ) := by
    rw [degree_eq_natDegree (mul_ne_zero hl (P.ne_zero i)), natDegree_mul hl (P.ne_zero i),
      hd, P.natDegree_eq]
    exact_mod_cast (show n - 1 + (i : ℕ) < 2 * n by omega)
  rw [hP.basis_repr_eq_integralInner_div hμ hpos]
  congr 1
  change (∫ y, l.eval y * (P i).eval y ∂μ) = _
  simp_rw [← eval_mul]
  rw [hP.integral_eq_sum_gaussWeight_mul_eval hμ hpos hdeg,
    Finset.sum_eq_single_of_mem x hx]
  · have hlx : l.eval x = 1 := Lagrange.eval_basis_self (fun _ _ _ _ h ↦ h) hx
    simp only [eval_mul, hlx, one_mul]
  · intro y hy hyx
    have hly : l.eval y = 0 := Lagrange.eval_basis_of_ne (v := id) hyx.symm hy
    simp only [eval_mul, hly, zero_mul, mul_zero]

/-- Gaussian weight times the squared evaluation-vector norm equals one. -/
theorem IsOrthogonal.gaussWeight_mul_sum_eval_sq {n : ℕ} {x : ℝ}
    (hx : x ∈ (P n).roots.toFinset) :
    ∑ i : Fin n, P.gaussWeight μ n x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) * ((P i).eval x ^ 2 / P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)) = 1 := by
  classical
  let l := Lagrange.basis (P n).roots.toFinset id x
  have hn : 0 < n := by
    rw [← hP.card_gaussNodes hμ hpos n]
    exact Finset.card_pos.mpr ⟨x, hx⟩
  have hd : l.degree < n := by
    have hl : l ≠ 0 := Lagrange.basis_ne_zero (fun _ _ _ _ h ↦ h) hx
    rw [degree_eq_natDegree hl]
    have he : l.natDegree = n - 1 := by
      simpa [l, hP.card_gaussNodes hμ hpos] using
        Lagrange.natDegree_basis (v := id) (fun _ _ _ _ h ↦ h) hx
    rw [he]
    exact_mod_cast (show n - 1 < n by omega)
  have he := congrArg (fun p : ℝ[X] ↦ p.eval x) (P.sum_fin_repr hd)
  simp only [eval_finsetSum, eval_smul, smul_eq_mul] at he
  have hv : l.eval x = 1 := Lagrange.eval_basis_self (fun _ _ _ _ h ↦ h) hx
  rw [hv] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (P.basis P.isUnit_leadingCoeff).repr
    (Lagrange.classicalBasis (P n).roots.toFinset id x (Lagrange.BasisInput.id _ _)) i * _
  rw [hP.gauss_lagrange_repr hμ hpos hx]
  ring

omit hμ hpos hP in
/-- Classical square-root and integral domains, only at actual vector coordinates.
The empty vector requires no weight or norm data. -/
structure GaussEigenvectorInput (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) (x : ℝ) where
  weight : Fin n → Lagrange.QuadratureInput μ (P n).roots.toFinset id x
  nonneg : ∀ i : Fin n, 0 ≤ P.gaussWeight μ n x (weight i)
  square : ∀ i : Fin n, IntegrableSquare μ (P i)
  positive : ∀ i : Fin n, 0 < P.squaredNorm μ i (square i)

omit hμ hpos hP in
/-- The coordinate square roots and their denominators lie in their classical domains. -/
theorem GaussEigenvectorInput.valid {P : Sequence ℝ} {μ : Measure ℝ} {n : ℕ} {x : ℝ}
    (d : GaussEigenvectorInput P μ n x) (i : Fin n) :
    0 ≤ P.gaussWeight μ n x (d.weight i) ∧ 0 < P.squaredNorm μ i (d.square i) :=
  ⟨d.nonneg i, d.positive i⟩

omit hμ hpos hP in
/-- Empty evaluation vectors require no integral or square-root data. -/
theorem GaussEigenvectorInput.empty (P : Sequence ℝ) (μ : Measure ℝ) (x : ℝ) :
    GaussEigenvectorInput P μ 0 x where
  weight i := Fin.elim0 i
  nonneg i := Fin.elim0 i
  square i := Fin.elim0 i
  positive i := Fin.elim0 i

/-- Gaussian nodes and positive polynomial integration supply classical vector data. -/
abbrev IsOrthogonal.gaussEigenvectorInput {n : ℕ} {x : ℝ}
    (hx : x ∈ (P n).roots.toFinset) : GaussEigenvectorInput P μ n x where
  weight _ := Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)
  nonneg _ := (hP.gaussWeight_pos hμ hpos hx).le
  square i := IntegrableSquare.of μ (P i) (hμ.integrable_mul _ _)
  positive i := squaredNorm_pos hpos P i

omit hμ hpos hP in
/-- The Gaussian evaluation vector in normalized polynomial coordinates (DLMF §3.5(vi)). -/
noncomputable def gaussEigenvector (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) (x : ℝ)
    (d : GaussEigenvectorInput P μ n x) : Fin n → ℝ :=
  fun i ↦ Real.sqrt (P.gaussWeight μ n x (d.weight i)) * (P i).eval x /
    Real.sqrt (P.squaredNorm μ i (d.square i))

omit hμ hpos hP in
/-- Classical coordinate formula for the Gaussian evaluation vector. -/
theorem gaussEigenvector_apply (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) (x : ℝ)
    (d : GaussEigenvectorInput P μ n x) (i : Fin n) :
    P.gaussEigenvector μ n x d i =
      Real.sqrt (P.gaussWeight μ n x (d.weight i)) * (P i).eval x /
        Real.sqrt (P.squaredNorm μ i (d.square i)) := rfl

/-- The evaluation vector has Euclidean squared norm one. -/
theorem IsOrthogonal.sum_sq_gaussEigenvector {n : ℕ} {x : ℝ}
    (hx : x ∈ (P n).roots.toFinset) :
    ∑ i : Fin n, P.gaussEigenvector μ n x (hP.gaussEigenvectorInput hμ hpos hx) i ^ 2 = 1 := by
  convert hP.gaussWeight_mul_sum_eval_sq hμ hpos hx using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [gaussEigenvector, div_pow, mul_pow,
    Real.sq_sqrt (hP.gaussWeight_pos hμ hpos hx).le,
    Real.sq_sqrt (squaredNorm_pos hpos P i).le]
  ring

omit hμ hpos hP in
/-- The squared norm of the constant polynomial is its value squared times mass. -/
theorem squaredNorm_zero_eq_mass (P : Sequence ℝ) (μ : Measure ℝ) (x : ℝ)
    (hi : Integrable (fun t => (P 0).eval t * (P 0).eval t) μ := by
      first
      | aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])
      | exact (Polynomial.HasPositiveDefiniteIntegral.hasFiniteMoments (by assumption)).integrable_mul _ _) :
    P.squaredNorm μ 0 (Polynomial.Sequence.IntegrableSquare.of _ _) = (P 0).eval x ^ 2 * μ.real Set.univ := by
  have he : P 0 = C ((P 0).coeff 0) := eq_C_of_natDegree_eq_zero (P.natDegree_eq 0)
  simp only [squaredNorm, integralInner]
  rw [he]
  simp only [eval_C, integral_const, smul_eq_mul, pow_two]
  ring

/-- Golub--Welsch's first-component formula for the canonical unit evaluation vector. -/
theorem IsOrthogonal.gaussWeight_eq_mass_mul_first_sq {n : ℕ} {x : ℝ}
    (hx : x ∈ (P (n + 1)).roots.toFinset) :
    P.gaussWeight μ (n + 1) x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) =
      μ.real Set.univ * (P.gaussEigenvector μ (n + 1) x (hP.gaussEigenvectorInput hμ hpos hx) 0) ^ 2 := by
  have hh := squaredNorm_pos hpos P 0
  have he := P.squaredNorm_zero_eq_mass μ x
  simp only [gaussEigenvector, Fin.val_zero, div_pow, mul_pow,
    Real.sq_sqrt (hP.gaussWeight_pos hμ hpos hx).le, Real.sq_sqrt hh.le]
  rw [← mul_div_assoc, eq_div_iff hh.ne']
  rw [he]
  ring

end Polynomial.Sequence
