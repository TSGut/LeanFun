/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Structure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Interlacing

import Mathlib.Tactic.Linarith

/-! # Real zeros and interlacing of Gegenbauer polynomials
Specialisation of general orthogonal-polynomial theory, with root location
transferred through the Jacobi bridge. Reference: DLMF 18.2(vi).
-/
public section
open MeasureTheory Set
namespace Polynomial
variable {lam : ℝ} (hlam : -(1 / 2) < lam) (hzero : lam ≠ 0)
include hlam hzero

/-- Gegenbauer polynomials split over the reals (DLMF 18.2(vi)). -/
theorem splits_gegenbauer (n : ℕ) : (gegenbauer lam n).Splits :=
  (isOrthogonal_gegenbauerSequence hlam hzero).splits (hasFiniteMoments_gegenbauerMeasure hlam)
    (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) n

/-- There are degree-many Gegenbauer roots (DLMF 18.2(vi)). -/
theorem card_roots_gegenbauer (n : ℕ) : (gegenbauer lam n).roots.card = n :=
  (isOrthogonal_gegenbauerSequence hlam hzero).card_roots (hasFiniteMoments_gegenbauerMeasure hlam)
    (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) n

/-- All Gegenbauer roots are simple (DLMF 18.2(vi)). -/
theorem separable_gegenbauer (n : ℕ) : (gegenbauer lam n).Separable :=
  (isOrthogonal_gegenbauerSequence hlam hzero).separable (hasFiniteMoments_gegenbauerMeasure hlam)
    (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) n

/-- Orthogonality to every lower-degree polynomial (DLMF 18.2(i)). -/
theorem integral_mul_gegenbauer_eq_zero_of_degree_lt {p : ℝ[X]} {n : ℕ} (hp : p.degree < n) :
    ∫ x, p.eval x * (gegenbauer lam n).eval x ∂gegenbauerMeasure lam = 0 :=
  (isOrthogonal_gegenbauerSequence hlam hzero).integralInner_eq_zero_of_degree_lt
    (hasFiniteMoments_gegenbauerMeasure hlam) hp

/-- Every Gegenbauer root lies strictly inside the interval (DLMF 18.2(vi)). -/
theorem root_gegenbauer_mem_Ioo {n : ℕ} {x : ℝ}
    (hx : (gegenbauer lam n).eval x = 0) : x ∈ Ioo (-1) 1 := by
  rw [gegenbauer_eq_jacobi_mul hlam, eval_mul, eval_C] at hx
  exact root_jacobi_mem_Ioo (by linarith) (by linarith)
    ((mul_eq_zero.mp hx).resolve_left (gegenbauer_jacobi_factor_ne_zero hlam hzero n))

/-- Consecutive members have no common root (DLMF 18.2(vi)). -/
theorem not_eval_gegenbauer_eq_zero_and_succ (n : ℕ) (x : ℝ) :
    ¬ ((gegenbauer lam n).eval x = 0 ∧ (gegenbauer lam (n + 1)).eval x = 0) :=
  (isOrthogonal_gegenbauerSequence hlam hzero).not_eval_eq_zero_and_succ
    (hasFiniteMoments_gegenbauerMeasure hlam)
    (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) n x

/-- Between degree-n roots lies a degree-(n+1) root (DLMF 18.2(vi)). -/
theorem exists_root_gegenbauer_succ_between (n : ℕ) {a b : ℝ} (hab : a < b)
    (ha : (gegenbauer lam n).eval a = 0) (hb : (gegenbauer lam n).eval b = 0) :
    ∃ c ∈ Ioo a b, (gegenbauer lam (n + 1)).eval c = 0 :=
  (isOrthogonal_gegenbauerSequence hlam hzero).exists_root_succ_between
    (hasFiniteMoments_gegenbauerMeasure hlam)
    (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) n hab ha hb

/-- Between degree-(n+1) roots lies a degree-n root (DLMF 18.2(vi)). -/
theorem exists_root_gegenbauer_between_succ (n : ℕ) {a b : ℝ} (hab : a < b)
    (ha : (gegenbauer lam (n + 1)).eval a = 0) (hb : (gegenbauer lam (n + 1)).eval b = 0) :
    ∃ c ∈ Ioo a b, (gegenbauer lam n).eval c = 0 :=
  (isOrthogonal_gegenbauerSequence hlam hzero).exists_root_between_succ
    (hasFiniteMoments_gegenbauerMeasure hlam)
    (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) n hab ha hb

/-- The higher-degree member has both outermost roots (DLMF 18.2(vi)). -/
theorem exists_outer_roots_gegenbauer {n : ℕ} (hn : 1 ≤ n) :
    ∃ a b : ℝ, a < b ∧ (gegenbauer lam (n + 1)).eval a = 0 ∧
      (gegenbauer lam (n + 1)).eval b = 0 ∧
      ∀ x : ℝ, (gegenbauer lam n).eval x = 0 → a < x ∧ x < b :=
  (isOrthogonal_gegenbauerSequence hlam hzero).exists_outer_roots
    (hasFiniteMoments_gegenbauerMeasure hlam)
    (hasPositiveDefiniteIntegral_gegenbauerMeasure hlam) hn

end Polynomial
