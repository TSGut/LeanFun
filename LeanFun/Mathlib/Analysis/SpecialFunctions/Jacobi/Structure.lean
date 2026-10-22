/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Orthogonality
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Interlacing
public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Symmetry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Real zeros and interlacing of Jacobi polynomials
Specialisation of general orthogonal-polynomial theory, with root location
proved using the support of the weight. Reference: DLMF 18.2(vi).
-/
public section
open MeasureTheory Set
namespace Polynomial
variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
include hα hβ

/-- Jacobi polynomials split over the reals (DLMF 18.2(vi)). -/
theorem splits_jacobi (n : ℕ) : (jacobi α β n).Splits :=
  (isOrthogonal_jacobiSequence hα hβ).splits (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) n

/-- There are degree-many Jacobi roots (DLMF 18.2(vi)). -/
theorem card_roots_jacobi (n : ℕ) : (jacobi α β n).roots.card = n :=
  (isOrthogonal_jacobiSequence hα hβ).card_roots (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) n

/-- All Jacobi roots are simple (DLMF 18.2(vi)). -/
theorem separable_jacobi (n : ℕ) : (jacobi α β n).Separable :=
  (isOrthogonal_jacobiSequence hα hβ).separable (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) n

/-- Orthogonality to every lower-degree polynomial (DLMF 18.2(i)). -/
theorem integral_mul_jacobi_eq_zero_of_degree_lt {p : ℝ[X]} {n : ℕ} (hp : p.degree < n) :
    ∫ x, p.eval x * (jacobi α β n).eval x ∂jacobiMeasure α β = 0 :=
  (isOrthogonal_jacobiSequence hα hβ).integralInner_eq_zero_of_degree_lt
    (hasFiniteMoments_jacobiMeasure hα hβ) hp

private theorem neg_one_lt_root_jacobi {n : ℕ} {r : ℝ} (hr : (jacobi α β n).eval r = 0) : -1 < r := by
  by_contra h
  have hrle : r ≤ -1 := le_of_not_gt h
  obtain ⟨q, hpq⟩ := dvd_iff_isRoot.mpr hr
  have hp : jacobi α β n ≠ 0 := (jacobiSequence hα hβ).ne_zero n
  have hq : q ≠ 0 := by intro hq; simp [hq] at hpq; exact hp hpq
  have hqd : q.degree < n := by
    rw [← degree_jacobi_of_neg_one_lt hα hβ n, hpq, degree_mul, degree_X_sub_C]
    rw [degree_eq_natDegree hq]
    exact_mod_cast (show q.natDegree < 1 + q.natDegree by omega)
  have hz := integral_mul_jacobi_eq_zero_of_degree_lt hα hβ hqd
  have he (x : ℝ) : q.eval x * (jacobi α β n).eval x = (x - r) * q.eval x ^ 2 := by
    rw [hpq, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hn : 0 ≤ᵐ[jacobiMeasure α β] fun x ↦ q.eval x * (jacobi α β n).eval x := by
    filter_upwards [ae_mem_Ioo_jacobiMeasure α β] with x hx
    rw [he]
    exact mul_nonneg (by linarith [hx.1]) (sq_nonneg _)
  have hzae := (integral_eq_zero_iff_of_nonneg_ae hn
    ((hasFiniteMoments_jacobiMeasure hα hβ).integrable_mul q (jacobi α β n))).mp hz
  have hqae : (fun x ↦ q.eval x ^ 2) =ᵐ[jacobiMeasure α β] 0 := by
    filter_upwards [hzae, ae_mem_Ioo_jacobiMeasure α β] with x hx hmem
    rw [he] at hx
    exact (mul_eq_zero.mp hx).resolve_left (by linarith [hmem.1])
  have hi := integral_congr_ae hqae
  exact (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ q hq).ne' (by simpa using hi)

/-- Every Jacobi root lies strictly inside the orthogonality interval (DLMF 18.2(vi)). -/
theorem root_jacobi_mem_Ioo {n : ℕ} {x : ℝ} (hx : (jacobi α β n).eval x = 0) :
    x ∈ Ioo (-1) 1 := by
  have hl := neg_one_lt_root_jacobi hα hβ hx
  have hn : (jacobi β α n).eval (-x) = 0 := by rw [eval_jacobi_neg, hx, mul_zero]
  have hr := neg_one_lt_root_jacobi hβ hα hn
  exact ⟨hl, by linarith⟩

/-- Consecutive members have no common root (DLMF 18.2(vi)). -/
theorem not_eval_jacobi_eq_zero_and_succ (n : ℕ) (x : ℝ) :
    ¬ ((jacobi α β n).eval x = 0 ∧ (jacobi α β (n + 1)).eval x = 0) :=
  (isOrthogonal_jacobiSequence hα hβ).not_eval_eq_zero_and_succ (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) n x

/-- Between degree-n roots lies a degree-(n+1) root (DLMF 18.2(vi)). -/
theorem exists_root_jacobi_succ_between (n : ℕ) {a b : ℝ} (hab : a < b)
    (ha : (jacobi α β n).eval a = 0) (hb : (jacobi α β n).eval b = 0) :
    ∃ c ∈ Ioo a b, (jacobi α β (n + 1)).eval c = 0 :=
  (isOrthogonal_jacobiSequence hα hβ).exists_root_succ_between (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) n hab ha hb

/-- Between degree-(n+1) roots lies a degree-n root (DLMF 18.2(vi)). -/
theorem exists_root_jacobi_between_succ (n : ℕ) {a b : ℝ} (hab : a < b)
    (ha : (jacobi α β (n + 1)).eval a = 0) (hb : (jacobi α β (n + 1)).eval b = 0) :
    ∃ c ∈ Ioo a b, (jacobi α β n).eval c = 0 :=
  (isOrthogonal_jacobiSequence hα hβ).exists_root_between_succ (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) n hab ha hb

/-- The higher-degree member has both outermost roots (DLMF 18.2(vi)). -/
theorem exists_outer_roots_jacobi {n : ℕ} (hn : 1 ≤ n) :
    ∃ a b : ℝ, a < b ∧ (jacobi α β (n + 1)).eval a = 0 ∧
      (jacobi α β (n + 1)).eval b = 0 ∧ ∀ x : ℝ, (jacobi α β n).eval x = 0 → a < x ∧ x < b :=
  (isOrthogonal_jacobiSequence hα hβ).exists_outer_roots (hasFiniteMoments_jacobiMeasure hα hβ)
    (hasPositiveDefiniteIntegral_jacobiMeasure hα hβ) hn

end Polynomial
