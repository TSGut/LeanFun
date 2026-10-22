/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraToeplitzSections
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraToeplitzAlgebra
public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.RealSymbolNorm

/-! # Toeplitz decompositions for norm limits of polynomial Volterra kernels

Uniform convergence of the physical kernel controls the diagonal Toeplitz
part; operator-norm convergence controls the compact remainder.
Reference: Gutleb's thesis, §2.7; Böttcher–Silbermann.
-/

@[expose] public noncomputable section
open Polynomial Set Filter ContinuousLinearMap
open scoped Topology InnerProductSpace
namespace MvPolynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2

private theorem diagonalSymbol_sub (p q : MvPolynomial (Fin 2) ℝ) :
    volterraDiagonalLaurentSymbol (p-q) =
      volterraDiagonalLaurentSymbol p-volterraDiagonalLaurentSymbol q := by
  let L : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] LaurentPolynomial ℝ :=
    (Finsupp.linearCombination ℝ (fun d : Fin 2 →₀ ℕ ↦
      shiftedJacobiLaurentSymbol^(d 0+d 1))).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap
  exact L.map_sub p q

/-- The supremum bound on a polynomial diagonal controls its Toeplitz part. -/
theorem norm_volterraDiagonalToeplitz_le (p : MvPolynomial (Fin 2) ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |eval (fun _ ↦ x) p| ≤ M) :
    ‖lp.laurentToeplitz (volterraDiagonalLaurentSymbol p)‖ ≤ M := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  apply lp.norm_laurentToeplitz_le_circle (T := 1) _ hM
  intro x
  rw [volterraDiagonalLaurentSymbol_circle, Complex.norm_real, Real.norm_eq_abs]
  exact hb _ (shiftedJacobiLaurentSymbol_circle_mem_Icc (T := ⟨1, one_ne_zero⟩) x)

/-- Uniform diagonal error bounds the difference of polynomial Toeplitz parts. -/
theorem norm_volterraDiagonalToeplitz_sub_le (p q : MvPolynomial (Fin 2) ℝ)
    {e : ℝ} (he : 0 ≤ e)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |eval (fun _ ↦ x) p-eval (fun _ ↦ x) q| ≤ e) :
    ‖lp.laurentToeplitz (volterraDiagonalLaurentSymbol p)-
      lp.laurentToeplitz (volterraDiagonalLaurentSymbol q)‖ ≤ e := by
  rw [← map_sub, ← diagonalSymbol_sub]
  exact norm_volterraDiagonalToeplitz_le (p-q) he (by simpa only [map_sub] using hb)

/-- Uniform approximation of the diagonal gives an operator-norm Toeplitz limit. -/
theorem exists_volterraDiagonalToeplitz_limit
    (K : (Fin 2 → ℝ) → ℝ) (p : ℕ → MvPolynomial (Fin 2) ℝ)
    {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n)
    (herr : ∀ n x, x ∈ Icc (0 : ℝ) 1 →
      |eval (fun _ ↦ x) (p n)-K (fun _ ↦ x)| ≤ e n)
    (hte : Tendsto e atTop (𝓝 0)) :
    ∃ T : H →L[ℝ] H,
      Tendsto (fun n ↦ lp.laurentToeplitz (volterraDiagonalLaurentSymbol (p n)))
        atTop (𝓝 T) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hte.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N,fun m hm n hn ↦ ?_⟩
  rw [dist_eq_norm]
  apply (norm_volterraDiagonalToeplitz_sub_le (p m) (p n)
    (add_nonneg (he m) (he n)) ?_).trans_lt (by linarith [hN m hm,hN n hn])
  intro x hx
  have hh := abs_add_le (eval (fun _ ↦ x) (p m)-K (fun _ ↦ x))
    (K (fun _ ↦ x)-eval (fun _ ↦ x) (p n))
  rw [sub_add_sub_cancel, abs_sub_comm (K (fun _ ↦ x))] at hh
  exact hh.trans (add_le_add (herr m x hx) (herr n x hx))

/-- Positive nonpolynomial diagonals give a coercive Toeplitz limit and compact remainder. -/
theorem exists_coercive_volterraToeplitz_limit
    (K : (Fin 2 → ℝ) → ℝ) (p : ℕ → MvPolynomial (Fin 2) ℝ)
    {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n)
    (herr : ∀ n x, x ∈ Icc (0 : ℝ) 1 →
      |eval (fun _ ↦ x) (p n)-K (fun _ ↦ x)| ≤ e n)
    (hte : Tendsto e atTop (𝓝 0))
    (A : H →L[ℝ] H) (hA : Tendsto (fun n ↦ volterraPreconditionedL2 (p n)) atTop (𝓝 A))
    {a : ℝ} (ha : 0 < a) (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, a ≤ K (fun _ ↦ x)) :
    ∃ T : H →L[ℝ] H, IsCompactOperator (A-T) ∧
      ∀ u : H, (a/2)*‖u‖^2 ≤ ⟪u,T u⟫_ℝ := by
  obtain ⟨T,hT⟩ := exists_volterraDiagonalToeplitz_limit K p he herr hte
  refine ⟨T,?_,?_⟩
  · exact isClosed_setOfPred_isCompactOperator.mem_of_tendsto (hA.sub hT)
      (Eventually.of_forall (fun n ↦ isCompactOperator_volterraPreconditionedL2_sub_symbol (p n)))
  · intro u
    have hc : Continuous (fun B : H →L[ℝ] H ↦ ⟪u,B u⟫_ℝ) := by fun_prop
    apply ge_of_tendsto (hc.continuousAt.tendsto.comp hT)
    filter_upwards [hte.eventually (gt_mem_nhds (half_pos ha))] with n hn
    apply inner_volterraDiagonalToeplitz_le (p n)
    intro x hx
    have hd := hdiag x hx
    have hp := (abs_le.mp (herr n x hx)).1
    linarith

end MvPolynomial
