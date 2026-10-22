/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.Polynomial.Jacobi.Rodrigues
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Weight
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.LinearCombination

/-!
# Weighted Jacobi Rodrigues formula

The identity is local on the open interval and holds for all real parameters;
no endpoint integrability is needed. Reference: DLMF 18.5.5, Table 18.5.1.
-/

public section
open Set Filter
open scoped Topology
namespace Polynomial

/-- The weighted lowering identity is a genuine derivative on the open domain
(DLMF 18.9.16). -/
theorem hasDerivAt_jacobiWeight_mul_jacobi (α β : ℝ) (n : ℕ)
    (x : Ioo (-1 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (jacobiWeight (α + 1) (β + 1) y : ℝ) *
        (jacobi (α + 1) (β + 1) n).eval (y : ℝ))
      (-2 * (n + 1 : ℝ) * (jacobiWeight α β x : ℝ) *
        (jacobi α β (n + 1)).eval (x : ℝ)) x := by
  have hP : HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
      (fun y ↦ (jacobi (α + 1) (β + 1) n).eval (y : ℝ))
      ((jacobi (α + 1) (β + 1) n).derivative.eval (x : ℝ)) x :=
    ⟨fun t ↦ (jacobi (α + 1) (β + 1) n).eval t, fun _ ↦ rfl,
      (jacobi (α + 1) (β + 1) n).hasDerivAt x⟩
  have hd := (hasDerivAt_jacobiWeight_add_one α β x).mul hP
  have he := congrArg (fun p : ℝ[X] ↦ p.eval (x : ℝ)) (jacobi_rodrigues_step α β n)
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_one, eval_X, eval_C, eval_neg] at he
  convert hd using 1
  rw [jacobiWeight_add_one α β x]
  linear_combination -(jacobiWeight α β x : ℝ) * he

/-- Rodrigues' formula with an actual chain of derivatives, for every real
parameter pair (DLMF 18.5.5). No endpoint regularity is required. -/
theorem hasIteratedDeriv_jacobiWeight (α β : ℝ) (n : ℕ) :
    HasIteratedDerivOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ n
      (fun x ↦ (jacobiWeight (α + n) (β + n) x : ℝ))
      (fun x ↦ (-2 : ℝ)^n * n.factorial * (jacobiWeight α β x : ℝ) *
        (jacobi α β n).eval (x : ℝ)) := by
  induction n generalizing α β with
  | zero =>
    change (fun x ↦ (jacobiWeight (α + (0 : ℕ)) (β + (0 : ℕ)) x : ℝ)) = _
    funext x
    simp
  | succ n ih =>
    refine ⟨fun x ↦ (-2 : ℝ)^n * n.factorial *
      (jacobiWeight (α+1) (β+1) x : ℝ) * (jacobi (α+1) (β+1) n).eval (x : ℝ), ?_, ?_⟩
    · have ha : α + ((n+1 : ℕ) : ℝ) = (α+1) + n := by push_cast; ring
      have hb : β + ((n+1 : ℕ) : ℝ) = (β+1) + n := by push_cast; ring
      simpa only [ha, hb] using ih (α+1) (β+1)
    · intro x
      have hd := (hasDerivAt_jacobiWeight_mul_jacobi α β n x).const_mul
        ((-2 : ℝ)^n * n.factorial)
      convert hd using 1
      · funext y
        ring
      · rw [pow_succ, Nat.factorial_succ]
        push_cast
        ring

/-- The divided Rodrigues representation includes existence of its numerator
as an iterated derivative (DLMF 18.5.5). -/
theorem eval_jacobi_eq_rodrigues (α β : ℝ) (n : ℕ) :
    ∃ d : Ioo (-1 : ℝ) 1 → ℝ,
      HasIteratedDerivOnOpen ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ n
        (fun x ↦ (jacobiWeight (α+n) (β+n) x : ℝ)) d ∧
      ∀ x : Ioo (-1 : ℝ) 1, (jacobi α β n).eval (x : ℝ) =
        d x / ((-2 : ℝ)^n * n.factorial * (jacobiWeight α β x : ℝ)) := by
  refine ⟨_, hasIteratedDeriv_jacobiWeight α β n, ?_⟩
  intro x
  have hd : (-2 : ℝ)^n * n.factorial * (jacobiWeight α β x : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))) (jacobiWeight_pos α β x).ne'
  exact (mul_div_cancel_left₀ _ hd).symm

end Polynomial
