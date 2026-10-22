/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.RecurrenceCoefficients

public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.LinearCombination

/-!
# Christoffel–Darboux for freely scaled orthogonal polynomial sequences

The first identity has the factor `x - y` cleared, so it holds also on the diagonal.
References: DLMF 18.2(v), https://dlmf.nist.gov/18.2#v; Szegő, Chapter 3.
-/

@[expose] public section

open MeasureTheory

namespace Polynomial.Sequence

/-- The classical finite kernel domain: only the selected polynomial squares
must be integrable with nonzero norm (DLMF 18.2(v)). -/
structure KernelInput (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) where
  square : ∀ i : Fin (n + 1), IntegrableSquare μ (P i)
  norm_ne : ∀ i : Fin (n + 1), P.squaredNorm μ i (square i) ≠ 0

/-- Construct a finite domain from available polynomial integrability and
nonzero-norm evidence. No values are supplied by this constructor. -/
abbrev KernelInput.of (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (hi : ∀ k, Integrable (fun t => (P k).eval t * (P k).eval t) μ := by
      intro k
      first
      | solve_by_elim (maxDepth := 4) [Polynomial.HasFiniteMoments.integrable_mul, Polynomial.Sequence.IsOrthogonal.integrable]
      | exact (Polynomial.HasPositiveDefiniteIntegral.hasFiniteMoments (by assumption)).integrable_mul _ _)
    (_hn : ∀ k, P.squaredNorm μ k (IntegrableSquare.of _ _) ≠ 0 := by
      intro k
      exact ne_of_gt (Polynomial.Sequence.squaredNorm_pos (by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) _ _)) :
    KernelInput P μ n :=
  ⟨fun i ↦ ⟨hi i⟩, fun i ↦ _hn i⟩

/-- Every selected kernel denominator is nonzero and has an integrable square. -/
theorem KernelInput.valid {P : Sequence ℝ} {μ : Measure ℝ} {n : ℕ}
    (d : KernelInput P μ n) (i : Fin (n + 1)) :
    Integrable (fun x ↦ (P i).eval x ^ 2) μ ∧ P.squaredNorm μ i (d.square i) ≠ 0 :=
  ⟨(d.square i).integrable_square, d.norm_ne i⟩

/-- The finite reproducing kernel on its classical input domain (DLMF 18.2.12). -/
noncomputable def kernel (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) (x y : ℝ)
    (d : KernelInput P μ n) : ℝ :=
  ∑ i : Fin (n + 1), (P i).eval x * (P i).eval y / P.squaredNorm μ i (d.square i)

/-- The classical finite sum formula for the kernel. -/
theorem kernel_apply (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) (x y : ℝ)
    (d : KernelInput P μ n) :
    P.kernel μ n x y d =
      ∑ i : Fin (n + 1), (P i).eval x * (P i).eval y / P.squaredNorm μ i (d.square i) := rfl

/-- Internal range-indexed bridge for globally supplied integrability evidence. -/
theorem kernel_of (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) (x y : ℝ)
    (hi : ∀ k, Integrable (fun t => (P k).eval t * (P k).eval t) μ)
    (hn : ∀ k, P.squaredNorm μ k (IntegrableSquare.of _ _) ≠ 0) :
    P.kernel μ n x y (KernelInput.of P μ n hi hn) =
      ∑ k ∈ Finset.range (n + 1),
        (P k).eval x * (P k).eval y / P.squaredNorm μ k (IntegrableSquare.of _ _) := by
  unfold kernel
  exact Fin.sum_univ_eq_sum_range
    (fun k ↦ (P k).eval x * (P k).eval y / P.squaredNorm μ k (IntegrableSquare.of _ _)) (n + 1)

/-- Internal range-sum bridge under positive definiteness. -/
theorem kernel_of_positive {μ : Measure ℝ} (hpos : HasPositiveDefiniteIntegral μ)
    (P : Sequence ℝ) (n : ℕ) (x y : ℝ) :
    P.kernel μ n x y (KernelInput.of P μ n
      (fun _ ↦ hpos.hasFiniteMoments.integrable_mul _ _)
      (fun k ↦ (squaredNorm_pos hpos P k).ne')) =
      ∑ k ∈ Finset.range (n + 1),
        (P k).eval x * (P k).eval y /
          P.squaredNorm μ k (IntegrableSquare.of _ _ (hpos.hasFiniteMoments.integrable_mul _ _)) :=
  kernel_of P μ n x y (fun _ ↦ hpos.hasFiniteMoments.integrable_mul _ _)
    (fun k ↦ (squaredNorm_pos hpos P k).ne')

/-- Christoffel–Darboux with the factor `x-y` cleared (DLMF 18.2.12). -/
theorem IsOrthogonal.christoffelDarboux {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (n : ℕ) (x y : ℝ) :
    (x - y) * P.kernel μ n x y (Polynomial.Sequence.KernelInput.of _ _ _) = P.recurrenceA n / P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _) *
      ((P (n + 1)).eval x * (P n).eval y - (P n).eval x * (P (n + 1)).eval y) := by
  induction n with
  | zero =>
    have hx := congrArg (fun p : ℝ[X] => p.eval x) (hP.two_term_zero hμ hpos)
    have hy := congrArg (fun p : ℝ[X] => p.eval y) (hP.two_term_zero hμ hpos)
    simp only [eval_mul, eval_X, eval_add, eval_smul, smul_eq_mul] at hx hy
    have h : (x - y) * (P 0).eval x * (P 0).eval y = P.recurrenceA 0 *
        ((P 1).eval x * (P 0).eval y - (P 0).eval x * (P 1).eval y) := by
      linear_combination (P 0).eval y * hx - (P 0).eval x * hy
    simp only [kernel_of_positive hpos P, Nat.zero_add, Finset.sum_range_one]
    calc
      _ = ((x - y) * (P 0).eval x * (P 0).eval y) / P.squaredNorm μ 0 (Polynomial.Sequence.IntegrableSquare.of _ _) := by ring
      _ = _ := by rw [h]; ring
  | succ n ih =>
    have hx := congrArg (fun p : ℝ[X] => p.eval x) (hP.three_term hμ hpos n)
    have hy := congrArg (fun p : ℝ[X] => p.eval y) (hP.three_term hμ hpos n)
    simp only [eval_mul, eval_X, eval_add, eval_smul, smul_eq_mul] at hx hy
    have h : (x - y) * (P (n + 1)).eval x * (P (n + 1)).eval y =
        P.recurrenceA (n + 1) * ((P (n + 2)).eval x * (P (n + 1)).eval y -
          (P (n + 1)).eval x * (P (n + 2)).eval y) -
        P.recurrenceC μ n (Sequence.RecurrenceCInput.of _ _ _) * ((P (n + 1)).eval x * (P n).eval y -
          (P n).eval x * (P (n + 1)).eval y) := by
      linear_combination (P (n + 1)).eval y * hx - (P (n + 1)).eval x * hy
    have hk : P.kernel μ (n + 1) x y (Polynomial.Sequence.KernelInput.of _ _ _) = P.kernel μ n x y (Polynomial.Sequence.KernelInput.of _ _ _) +
        (P (n + 1)).eval x * (P (n + 1)).eval y / P.squaredNorm μ (n + 1) (Polynomial.Sequence.IntegrableSquare.of _ _) := by
      simp only [kernel_of_positive hpos P]
      exact Finset.sum_range_succ _ _
    rw [hk, mul_add, ih]
    rw [show (x - y) * ((P (n + 1)).eval x * (P (n + 1)).eval y /
      P.squaredNorm μ (n + 1) (Polynomial.Sequence.IntegrableSquare.of _ _)) =
      ((x - y) * (P (n + 1)).eval x * (P (n + 1)).eval y) /
      P.squaredNorm μ (n + 1) (Polynomial.Sequence.IntegrableSquare.of _ _) by ring, h]
    simp only [recurrenceC]
    field_simp [ne_of_gt (squaredNorm_pos hpos P n),
      ne_of_gt (squaredNorm_pos hpos P (n + 1))]
    ring

/-- The diagonal Christoffel–Darboux identity (DLMF 18.2.13). -/
theorem IsOrthogonal.christoffelDarboux_diag {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (n : ℕ) (x : ℝ) :
    P.kernel μ n x x (Polynomial.Sequence.KernelInput.of _ _ _) = P.recurrenceA n / P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _) *
      ((P (n + 1)).derivative.eval x * (P n).eval x -
        (P n).derivative.eval x * (P (n + 1)).eval x) := by
  have hk : DifferentiableAt ℝ (fun y => P.kernel μ n y x (Polynomial.Sequence.KernelInput.of _ _ _)) x := by
    unfold kernel
    exact DifferentiableAt.fun_sum fun k _ =>
      (((P k).differentiableAt).mul_const ((P k).eval x)).div_const _
  have hid : HasDerivAt (fun y : ℝ => y - x) 1 x := (hasDerivAt_id x).sub_const x
  have hl := hid.mul hk.hasDerivAt
  have hr := ((((P (n + 1)).hasDerivAt x).mul_const ((P n).eval x)).sub
    (((P n).hasDerivAt x).mul_const ((P (n + 1)).eval x))).const_mul
      (P.recurrenceA n / P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _))
  have heq : (fun y => (y - x) * P.kernel μ n y x (Polynomial.Sequence.KernelInput.of _ _ _)) =
      (fun y => P.recurrenceA n / P.squaredNorm μ n (Polynomial.Sequence.IntegrableSquare.of _ _) *
        ((P (n + 1)).eval y * (P n).eval x -
          (P n).eval y * (P (n + 1)).eval x)) :=
    _root_.funext fun y => hP.christoffelDarboux hμ hpos n y x
  change HasDerivAt (fun y => (y - x) * P.kernel μ n y x (Polynomial.Sequence.KernelInput.of _ _ _)) _ x at hl
  rw [heq] at hl
  simpa using hl.unique hr

/-- The degree-zero member never vanishes (Szegő, Chapter 3). -/
theorem eval_zero_ne_zero (P : Sequence ℝ) (x : ℝ) : (P 0).eval x ≠ 0 := by
  have hp := eq_C_of_natDegree_eq_zero (P.natDegree_eq 0)
  rw [hp, eval_C]
  intro h
  exact P.ne_zero 0 (by rw [hp, h, C_0])

/-- The diagonal kernel is strictly positive (DLMF 18.2.13). -/
theorem kernel_diag_pos {μ : Measure ℝ} (hpos : HasPositiveDefiniteIntegral μ)
    (P : Sequence ℝ) (n : ℕ) (x : ℝ) : 0 < P.kernel μ n x x (Polynomial.Sequence.KernelInput.of _ _ _) := by
  simp only [kernel_of_positive hpos P]
  apply Finset.sum_pos'
  · intro k _
    exact div_nonneg (mul_self_nonneg _) (le_of_lt (squaredNorm_pos hpos P k))
  · exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n),
      div_pos (mul_self_pos.mpr (eval_zero_ne_zero P x)) (squaredNorm_pos hpos P 0)⟩

/-- Consecutive orthogonal polynomials have a nowhere-zero Wronskian
(DLMF 18.2.13). -/
theorem IsOrthogonal.wronskian_ne_zero {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (n : ℕ) (x : ℝ) :
    (P (n + 1)).derivative.eval x * (P n).eval x -
      (P n).derivative.eval x * (P (n + 1)).eval x ≠ 0 := by
  intro h
  have heq := hP.christoffelDarboux_diag hμ hpos n x
  rw [h, mul_zero] at heq
  exact (ne_of_gt (kernel_diag_pos hpos P n x)) heq

/-- Consecutive members have no common real root (Szegő, Chapter 3). -/
theorem IsOrthogonal.not_eval_eq_zero_and_succ {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ) (x : ℝ) :
    ¬ ((P n).eval x = 0 ∧ (P (n + 1)).eval x = 0) := by
  rintro ⟨hn, hs⟩
  exact hP.wronskian_ne_zero hμ hpos n x (by rw [hn, hs]; ring)

/-- Every real root is simple: the derivative does not vanish there
(Szegő, Chapter 3). -/
theorem IsOrthogonal.derivative_eval_ne_zero {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ) (x : ℝ)
    (hx : (P n).eval x = 0) : (P n).derivative.eval x ≠ 0 := by
  cases n with
  | zero => exact (eval_zero_ne_zero P x hx).elim
  | succ n =>
    intro hd
    exact hP.wronskian_ne_zero hμ hpos n x (by rw [hx, hd]; ring)

end Polynomial.Sequence
