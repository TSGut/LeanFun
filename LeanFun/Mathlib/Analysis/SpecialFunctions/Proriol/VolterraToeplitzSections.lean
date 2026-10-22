/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraToeplitz
public import LeanFun.Mathlib.Analysis.InnerProductSpace.CoerciveSections
public import LeanFun.Mathlib.Analysis.Normed.Operator.CompactInjective

/-! # Conditional stability of polynomial Volterra Toeplitz sections

Diagonal positivity certifies the symbol. Injectivity of the ordered operator
is an explicit assumption until the integral injectivity bridge is proved.
Reference: Gutleb's thesis, §2.7; Böttcher--Silbermann, finite-section stability.
-/

@[expose] public noncomputable section
open ContinuousLinearMap Filter
open scoped Topology InnerProductSpace
namespace MvPolynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2

/-- A lower bound on the kernel diagonal controls the real Toeplitz quadratic form. -/
theorem inner_volterraDiagonalToeplitz_le (K : MvPolynomial (Fin 2) ℝ) {a : ℝ}
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, a ≤ eval (fun _ ↦ x) K) (u : H) :
    a*‖u‖^2 ≤ ⟪u, lp.laurentToeplitz (volterraDiagonalLaurentSymbol K) u⟫_ℝ := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  apply lp.inner_laurentToeplitz_le (T := 1)
  intro x
  rw [volterraDiagonalLaurentSymbol_circle, Complex.ofReal_re]
  exact hK _ (Polynomial.shiftedJacobiLaurentSymbol_circle_mem_Icc (T := ⟨1, one_ne_zero⟩) x)

/-- Under diagonal positivity, injectivity makes the ordered coefficient operator invertible. -/
theorem isUnit_volterraPreconditionedL2_of_injective (K : MvPolynomial (Fin 2) ℝ)
    {a : ℝ} (ha : 0 < a)
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, a ≤ eval (fun _ ↦ x) K)
    (hinj : Function.Injective (volterraPreconditionedL2 K)) :
    IsUnit (volterraPreconditionedL2 K) := by
  let A := lp.laurentToeplitz (volterraDiagonalLaurentSymbol K)
  have hA : IsUnit A := isUnit_of_re_inner_le A ha (inner_volterraDiagonalToeplitz_le K hK)
  have he : A+(volterraPreconditionedL2 K-A) = volterraPreconditionedL2 K := by abel
  rw [← he]
  apply isUnit_add_of_injective_of_compact _ _ hA
    (isCompactOperator_volterraPreconditionedL2_sub_symbol K)
  change Function.Injective (A+(volterraPreconditionedL2 K-A))
  rw [he]
  exact hinj

/-- Positive diagonal and injectivity give eventually invertible finite sections. -/
theorem eventually_isUnit_volterraPreconditionedL2_section (K : MvPolynomial (Fin 2) ℝ)
    {a : ℝ} (ha : 0 < a)
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, a ≤ eval (fun _ ↦ x) K)
    (hinj : Function.Injective (volterraPreconditionedL2 K)) :
    ∀ᶠ N in atTop, IsUnit (coerciveFiniteSection (lp.initialL2Projection N)
      (volterraPreconditionedL2 K)) := by
  have hb (u : H) : min a 1*‖u‖^2 ≤
      RCLike.re ⟪u, lp.laurentToeplitz (volterraDiagonalLaurentSymbol K) u⟫_ℝ :=
    (mul_le_mul_of_nonneg_right (min_le_left a 1) (sq_nonneg ‖u‖)).trans
      (inner_volterraDiagonalToeplitz_le K hK u)
  have he : lp.laurentToeplitz (volterraDiagonalLaurentSymbol K)+
      (volterraPreconditionedL2 K-lp.laurentToeplitz (volterraDiagonalLaurentSymbol K)) =
      volterraPreconditionedL2 K := by abel
  have hu := isUnit_volterraPreconditionedL2_of_injective K ha hK hinj
  rw [← he] at hu ⊢
  exact lp.eventually_isUnit_coerciveFiniteSection_add_compact _ _
    (lt_min ha zero_lt_one) (min_le_right a 1) hb
    (isCompactOperator_volterraPreconditionedL2_sub_symbol K) hu

/-- Under the explicit injectivity hypothesis, the projected coefficient solves converge. -/
theorem tendsto_volterraPreconditionedL2_section_solution (K : MvPolynomial (Fin 2) ℝ)
    {a : ℝ} (ha : 0 < a)
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, a ≤ eval (fun _ ↦ x) K)
    (hinj : Function.Injective (volterraPreconditionedL2 K)) (g : H) :
    Tendsto (fun N ↦ Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
      (volterraPreconditionedL2 K)) (lp.initialL2Projection N g)) atTop
      (𝓝 (Ring.inverse (volterraPreconditionedL2 K) g)) := by
  have hb (u : H) : min a 1*‖u‖^2 ≤
      RCLike.re ⟪u, lp.laurentToeplitz (volterraDiagonalLaurentSymbol K) u⟫_ℝ :=
    (mul_le_mul_of_nonneg_right (min_le_left a 1) (sq_nonneg ‖u‖)).trans
      (inner_volterraDiagonalToeplitz_le K hK u)
  have he : lp.laurentToeplitz (volterraDiagonalLaurentSymbol K)+
      (volterraPreconditionedL2 K-lp.laurentToeplitz (volterraDiagonalLaurentSymbol K)) =
      volterraPreconditionedL2 K := by abel
  have hu := isUnit_volterraPreconditionedL2_of_injective K ha hK hinj
  rw [← he] at hu ⊢
  exact lp.tendsto_coerciveFiniteSection_add_compact_solution _ _
    (lt_min ha zero_lt_one) (min_le_right a 1) hb
    (isCompactOperator_volterraPreconditionedL2_sub_symbol K) hu g

end MvPolynomial
