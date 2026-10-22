/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.UniformApproximation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ChristoffelDarboux
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Christoffel kernel bounds for weighted projection

The existing Christoffel--Darboux kernel controls polynomial evaluation and
pointwise projection errors. References: DLMF 18.2(v), (viii); ATAP, Chapter 16.
-/

public section
open Real MeasureTheory
open scoped InnerProductSpace
namespace Polynomial.Sequence
variable {μ : Measure ℝ} {P : Sequence ℝ} (hμ : HasFiniteMoments μ)

/-- The L² vector representing evaluation of the degree-N projection at x. -/
@[expose] noncomputable def kernelVector (P : Sequence ℝ)
    (N : {N : ℕ // ∀ i ≤ N, 0 < P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)}) (x : ℝ) : Lp ℝ 2 μ :=
  ∑ i : Fin (N.val + 1), ((P i).eval x / √(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _))) •
    P.normalizedToL2 hμ ⟨i, N.property i (Nat.le_of_lt_succ i.isLt)⟩

/-- Classical finite kernel-vector formula (DLMF 18.2(v)). -/
theorem kernelVector_apply (P : Sequence ℝ)
    (N : {N : ℕ // ∀ i ≤ N, 0 < P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)}) (x : ℝ) :
    P.kernelVector hμ N x =
      ∑ i : Fin (N.val + 1), ((P i).eval x / √(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _))) •
        P.normalizedToL2 hμ ⟨i, N.property i (Nat.le_of_lt_succ i.isLt)⟩ := rfl

/-- Internal range-indexed formula under positive definiteness. -/
theorem kernelVector_of_positive (P : Sequence ℝ) (hpos : HasPositiveDefiniteIntegral μ)
    (N : ℕ) (x : ℝ) :
    P.kernelVector hμ ⟨N, fun i _ ↦ squaredNorm_pos hpos P i⟩ x =
      ∑ i ∈ Finset.range (N + 1), ((P i).eval x / √(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _))) •
        P.normalizedToL2 hμ ⟨i, squaredNorm_pos hpos P i⟩ := by
  unfold kernelVector
  exact Fin.sum_univ_eq_sum_range (fun i ↦ ((P i).eval x / √(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _))) •
    P.normalizedToL2 hμ ⟨i, squaredNorm_pos hpos P i⟩) (N + 1)

include hμ

/-- The kernel vector reproduces the polynomial partial sum. -/
theorem inner_kernelVector (hpos : HasPositiveDefiniteIntegral μ)
    (N : ℕ) (x : ℝ) (f : Lp ℝ 2 μ) :
    inner ℝ (P.kernelVector hμ ⟨N, fun i _ ↦ squaredNorm_pos hpos P i⟩ x) f = (P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N)).eval x := by
  simp only [kernelVector_of_positive hμ P hpos, partialSum_ofL2, sum_inner, inner_smul_left, conj_trivial,
    normalizedToL2, inner_smul_left, inner_polynomialToL2_left,
    eval_finsetSum, eval_smul, smul_eq_mul, integralCoefficient, IntegralCoefficientInput.ofL2]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (P i).eval x * ((√(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹ * (√(P.squaredNorm μ i (Polynomial.Sequence.IntegrableSquare.of _ _)))⁻¹) *
        (∫ t, f t * (P i).eval t ∂μ) := by ring
    _ = _ := by
      rw [← mul_inv, Real.mul_self_sqrt (squaredNorm_pos hpos P i).le]
      ring

/-- The squared norm of the representing vector is the diagonal kernel. -/
theorem IsOrthogonal.norm_kernelVector_sq (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (N : ℕ) (x : ℝ) :
    ‖P.kernelVector hμ ⟨N, fun i _ ↦ squaredNorm_pos hpos P i⟩ x‖ ^ 2 = P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _) := by
  rw [← real_inner_self_eq_norm_sq, kernelVector_of_positive hμ P hpos,
    (hP.orthonormal_normalizedToL2 hμ hpos).inner_sum]
  simp only [kernel_of_positive hpos P, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_mul_div_comm, Real.mul_self_sqrt (squaredNorm_pos hpos P i).le]

/-- The norm of the representing vector is the square root of the diagonal kernel. -/
theorem IsOrthogonal.norm_kernelVector (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (N : ℕ) (x : ℝ) :
    ‖P.kernelVector hμ ⟨N, fun i _ ↦ squaredNorm_pos hpos P i⟩ x‖ = √(P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _)) := by
  rw [← hP.norm_kernelVector_sq hμ hpos, Real.sqrt_sq (norm_nonneg _)]

/-- Christoffel's pointwise bound for the projected polynomial. -/
theorem IsOrthogonal.norm_eval_partialSum_le_kernel (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (f : Lp ℝ 2 μ) (N : ℕ) (x : ℝ) :
    ‖(P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N)).eval x‖ ≤ √(P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _)) * ‖f‖ := by
  rw [← inner_kernelVector hμ hpos]
  exact (norm_inner_le_norm _ _).trans_eq
    (by rw [hP.norm_kernelVector hμ hpos])

/-- A polynomial of degree at most N is bounded pointwise by its weighted L²
norm times the square root of the diagonal Christoffel kernel. -/
theorem IsOrthogonal.norm_eval_le_kernel_mul_norm (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (N : ℕ) (p : ℝ[X]) (hp : p.degree ≤ N) (x : ℝ) :
    ‖p.eval x‖ ≤ √(P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _)) * ‖polynomialToL2 hμ p‖ := by
  simpa only [hP.partialSum_polynomialToL2 hμ hpos N p hp] using
    hP.norm_eval_partialSum_le_kernel hμ hpos (polynomialToL2 hμ p) N x

/-- A uniform competitor yields a pointwise projection error controlled by the
Christoffel kernel. No asymptotic growth bound on the kernel is assumed. -/
theorem IsOrthogonal.norm_sub_eval_partialSum_le_kernel (hP : P.IsOrthogonal μ)
    (hpos : HasPositiveDefiniteIntegral μ) (f : Lp ℝ 2 μ) (N : ℕ)
    (p : ℝ[X]) (hp : p.degree ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ᵐ t ∂μ, ‖f t - p.eval t‖ ≤ ε) (x y : ℝ)
    (hx : ‖y - p.eval x‖ ≤ ε) :
    ‖y - (P.partialSum μ (IntegralCoefficientFamilyInput.ofL2 hμ hpos P f N)).eval x‖ ≤
      (1 + √(P.kernel μ N x x (Polynomial.Sequence.KernelInput.of _ _ _)) * √(μ.real Set.univ)) * ε := by
  exact hP.norm_sub_eval_partialSum_le_of_polynomial_bound hμ hpos f N p hp hε
    (Real.sqrt_nonneg _) he x y hx
    (fun q hq ↦ hP.norm_eval_le_kernel_mul_norm hμ hpos N q hq x)

end Polynomial.Sequence
