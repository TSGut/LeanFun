/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Order.ClassicalSupremum
public import LeanFun.Mathlib.Analysis.FiniteReciprocalSum
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ExtremaBounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Lebesgue constants for Chebyshev extrema

We prove the explicit nonsharp estimate `Λ_N ≤ 2π + 2 + 2 log N` for `N ≥ 1`,
and `Λ_0 = 1`. Boundedness is proved before using the real supremum.
Reference: ATAP, Chapters 15--16.
-/

@[expose] public section
namespace Polynomial.Chebyshev
open Real Set

/-- The sum of absolute cardinal polynomials (ATAP, Chapter 15). -/
noncomputable def extremaLebesgueFunction (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j : Fin (N + 1), ‖(extremaCardinal N j).eval (x : ℂ)‖


/-- Classical finite-cardinal-sum formula (ATAP Chapter 15). -/
theorem extremaLebesgueFunction_apply (N : ℕ) (x : ℝ) :
    extremaLebesgueFunction N x = ∑ j : Fin (N + 1),
      ‖(extremaCardinal N j).eval (x : ℂ)‖ := rfl

/-- The order-zero Lebesgue function is one (ATAP, Chapter 15). -/
@[simp] theorem extremaLebesgueFunction_zero (x : ℝ) : extremaLebesgueFunction 0 x = 1 := by
  simp [extremaLebesgueFunction, extremaCardinal_zero]

/-- The Lebesgue function is nonnegative (ATAP, Chapter 15). -/
theorem extremaLebesgueFunction_nonneg (N : ℕ) (x : ℝ) : 0 ≤ extremaLebesgueFunction N x :=
  Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)

private theorem lebesgue_positive (N : {n : ℕ // 0 < n}) (x : ℝ) :
    extremaLebesgueFunction N.val x = ∑ j ∈ Finset.range (N.val+1),
      |(Lagrange.basis (Finset.range (N.val+1)) (classicalNode N) j).eval x| := by
  have he (j : Fin (N.val+1)) :
      (extremaCardinal N.val j).eval (x : ℂ) =
        (((Lagrange.classicalBasis (Finset.range (N.val+1)) (classicalNode N) j
          (Lagrange.BasisInput.of_injOn (strictAntiOn_classicalNode N).injOn
            (Finset.mem_range.mpr j.isLt))).eval x : ℝ) : ℂ) := by
    rw [extremaCardinal_positive N]
    exact Lagrange.eval_classicalBasis_complex _ _ j _ x
  simp only [extremaLebesgueFunction, he, Complex.norm_real, Real.norm_eq_abs,
    Lagrange.classicalBasis]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    |(Lagrange.basis (Finset.range (N.val+1)) (classicalNode N) j).eval x|) (N.val+1)
/-- A harmonic upper bound for the Lebesgue function (ATAP, Chapter 15, nonsharp). -/
theorem extremaLebesgueFunction_le_harmonic (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    extremaLebesgueFunction N x ≤ 2 * π + 2 * (harmonic N : ℝ) := by
  by_cases hN : N = 0
  · subst N
    simp only [extremaLebesgueFunction_zero, harmonic_zero, Rat.cast_zero, mul_zero, add_zero]
    linarith [two_le_pi]
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  let θ := arccos x
  have hθ : θ ∈ Icc 0 π := ⟨arccos_nonneg x, arccos_le_pi x⟩
  have hcos : cos θ = x := cos_arccos hx.1 hx.2
  let t := (N : ℝ) * θ / π
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg hn.le hθ.1) pi_pos.le
  have htN : t ≤ N := by
    dsimp [t]
    apply (div_le_iff₀ pi_pos).mpr
    exact mul_le_mul_of_nonneg_left hθ.2 hn.le
  rw [lebesgue_positive ⟨N,Nat.pos_of_ne_zero hN⟩]
  change (∑ j ∈ Finset.range (N+1),
    |(Lagrange.basis (Finset.range (N+1)) (node N) j).eval x|) ≤
      2 * π + 2 * (harmonic N : ℝ)
  apply Finset.sum_le_two_mul_add_harmonic ht0 htN pi_pos.le
  · intro j _; exact abs_nonneg _
  · intro j hj
    simpa only [hcos] using abs_eval_extremaBasis_cos_le_pi hN hj hθ
  · intro j hj
    have h := abs_eval_extremaBasis_mul_angle_le hN hj hθ
    have he : (N : ℝ) * |θ - (j : ℝ) * π / N| = π * |t - j| := by
      calc
        _ = |(N : ℝ) * (θ - (j : ℝ) * π / N)| := by
          rw [abs_mul, abs_of_pos hn]
        _ = |π * (t - j)| := by
          congr 1
          dsimp [t]
          field_simp
        _ = _ := by rw [abs_mul, abs_of_pos pi_pos]
    rw [mul_assoc, he, hcos] at h
    have h' := (mul_le_mul_of_nonneg_left (abs_sin_le_one ((N : ℝ) * θ)) pi_pos.le)
    apply (mul_le_mul_iff_left₀ pi_pos).mp
    nlinarith

/-- Explicit logarithmic growth on the entire closed interval (ATAP, Chapter 15,
nonsharp constants). -/
theorem extremaLebesgueFunction_le_log {N : ℕ} (hN : N ≠ 0) {x : ℝ}
    (hx : x ∈ Icc (-1) 1) :
    extremaLebesgueFunction N x ≤ 2 * π + 2 + 2 * log N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  linarith [extremaLebesgueFunction_le_harmonic (n + 1) hx, harmonic_le_one_add_log (n + 1)]

/-- The family defining the real supremum is bounded above (ATAP, Chapter 15). -/
theorem bddAbove_extremaLebesgueFunction (N : ℕ) :
    BddAbove (extremaLebesgueFunction N '' Icc (-1) 1) := by
  refine ⟨2 * π + 2 * (harmonic N : ℝ), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact extremaLebesgueFunction_le_harmonic N hx

/-- The certified classical supremum domain of the Lebesgue function. -/
noncomputable def extremaLebesgueSupremumInput (N : ℕ) : Real.SupremumInput where
  carrier := extremaLebesgueFunction N '' Icc (-1) 1
  nonempty := ⟨extremaLebesgueFunction N 0, 0, by norm_num, rfl⟩
  bounded := bddAbove_extremaLebesgueFunction N

/-- The classical Lebesgue constant (ATAP Chapters 15--16). -/
noncomputable def extremaLebesgueConstant (N : ℕ) : ℝ :=
  Real.classicalSup (extremaLebesgueSupremumInput N)

/-- The Lebesgue constant is the genuine least upper bound. -/
theorem extremaLebesgueConstant_isLUB (N : ℕ) :
    IsLUB (extremaLebesgueFunction N '' Icc (-1) 1) (extremaLebesgueConstant N) :=
  Real.classicalSup_isLUB (extremaLebesgueSupremumInput N)

/-- Every pointwise value is below the genuine bounded supremum (ATAP, Chapter 15). -/
theorem extremaLebesgueFunction_le_constant (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    extremaLebesgueFunction N x ≤ extremaLebesgueConstant N :=
  le_csSup (bddAbove_extremaLebesgueFunction N) ⟨x, hx, rfl⟩

/-- The order-zero Lebesgue constant is one (ATAP, Chapter 15). -/
@[simp] theorem extremaLebesgueConstant_zero : extremaLebesgueConstant 0 = 1 := by
  apply le_antisymm
  · apply csSup_le (Set.Nonempty.image _ (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩))
    rintro _ ⟨x, hx, rfl⟩
    simp
  · simpa using extremaLebesgueFunction_le_constant 0 (x := 0) (by norm_num)

/-- An explicit logarithmic Lebesgue-constant bound for positive order
(ATAP, Chapter 15, nonsharp constants). -/
theorem extremaLebesgueConstant_le_log {N : ℕ} (hN : N ≠ 0) :
    extremaLebesgueConstant N ≤ 2 * π + 2 + 2 * log N := by
  apply csSup_le (Set.Nonempty.image _ (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩))
  rintro _ ⟨x, hx, rfl⟩
  exact extremaLebesgueFunction_le_log hN hx

end Polynomial.Chebyshev
