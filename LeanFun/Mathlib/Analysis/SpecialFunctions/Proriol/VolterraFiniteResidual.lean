/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraRawAssembly
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraSupport

/-! # Finite residuals for raw Volterra solves

The exact rectangular Proriol assembly recovers every nonzero raw residual row.
Reference: Gutleb's thesis, §§2.3 and 2.7.
-/
@[expose] public noncomputable section
open Polynomial
local notation "E" => lp (fun _ : ℕ ↦ ℝ) 2

private theorem norm_eq_finite_sum (u : E) (M : ℕ) (hu : ∀ n, M ≤ n → u n = 0) :
    ‖u‖ = Real.sqrt (∑ n ∈ Finset.range M, (u n)^2) := by
  rw [← Real.sqrt_sq (norm_nonneg u),lp.norm_sq_eq_tsum_sq]
  congr 1
  rw [tsum_eq_sum (s := Finset.range M) (fun n hn ↦ by
    rw [hu n (by simpa only [Finset.mem_range,not_lt] using hn),norm_zero,zero_pow (by decide)])]
  simp only [Real.norm_eq_abs,sq_abs]

namespace lp
/-- A finitely supported raw coefficient norm is an ordinary finite Euclidean norm. -/
theorem norm_finsuppL2_eq_sqrt_sum (c : ℕ →₀ ℝ) (N : ℕ)
    (hc : ∀ n ∈ c.support, n < N) :
    ‖finsuppL2 c‖ = Real.sqrt (∑ n ∈ Finset.range N, (c n)^2) := by
  apply norm_eq_finite_sum
  intro n hn
  exact Finsupp.notMem_support_iff.mp (fun h ↦ (Nat.not_lt_of_ge hn) (hc n h))
end lp
namespace MvPolynomial

/-- Undoing the integration diagonal gives raw ordered coefficients from Proriol assembly. -/
theorem volterraPreconditionedL2_finsupp_apply (K : MvPolynomial (Fin 2) ℝ)
    (c : ℕ →₀ ℝ) (n : ℕ) :
    volterraPreconditionedL2 K (lp.finsuppL2 c) n =
      (-1 : ℝ)^n*((n : ℝ)+1)*volterraProriolCoefficients K c n := by
  have h := congrArg (fun u : E ↦ u n) (volterraRawDiagonal_preconditioned_finsupp K c)
  rw [volterraRawDiagonal_apply,lp.finsuppL2_apply] at h
  have ht : (n : ℝ)+1 ≠ 0 := by positivity
  have hs : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by rw [← mul_pow]; norm_num
  have he : (-1 : ℝ)^n * volterraPreconditionedL2 K (lp.finsuppL2 c) n =
      volterraProriolCoefficients K c n * ((n : ℝ)+1) := by
    apply (div_eq_iff ht).mp
    simpa only [div_mul_eq_mul_div] using h
  calc
    _ = (-1 : ℝ)^n*((-1 : ℝ)^n*volterraPreconditionedL2 K (lp.finsuppL2 c) n) := by
      rw [← mul_assoc,hs,one_mul]
    _ = _ := by rw [he]; ring

/-- Raw preconditioning preserves the rectangular degree cutoff. -/
theorem volterraPreconditionedL2_finsupp_cutoff (K : MvPolynomial (Fin 2) ℝ)
    (c : ℕ →₀ ℝ) (N : ℕ) (hc : ∀ n ∈ c.support, n < N)
    (i : ℕ) (hi : N+K.totalDegree ≤ i) :
    volterraPreconditionedL2 K (lp.finsuppL2 c) i = 0 := by
  rw [volterraPreconditionedL2_finsupp_apply,volterraProriolCoefficients_cutoff K N c hc i hi,mul_zero]

/-- The raw polynomial-kernel residual vanishes outside the indicated rectangular cutoff. -/
theorem volterraFiniteResidual_cutoff (K : MvPolynomial (Fin 2) ℝ)
    (c d : ℕ →₀ ℝ) (N M : ℕ) (hc : ∀ n ∈ c.support, n < N)
    (hd : ∀ n ∈ d.support, n < M) (i : ℕ) (hi : max M (N+K.totalDegree) ≤ i) :
    (lp.finsuppL2 d-volterraPreconditionedL2 K (lp.finsuppL2 c)) i = 0 := by
  have hd0 : d i = 0 := Finsupp.notMem_support_iff.mp
    (fun h ↦ (Nat.not_lt_of_ge ((le_max_left _ _).trans hi)) (hd i h))
  simp only [lp.coeFn_sub,Pi.sub_apply,lp.finsuppL2_apply,hd0,
    volterraPreconditionedL2_finsupp_cutoff K c N hc i ((le_max_right _ _).trans hi),sub_self]

/-- The full raw residual norm is exactly a finite sum, including rows beyond the solved section. -/
theorem norm_volterraFiniteResidual_eq (K : MvPolynomial (Fin 2) ℝ)
    (c d : ℕ →₀ ℝ) (N M : ℕ) (hc : ∀ n ∈ c.support, n < N)
    (hd : ∀ n ∈ d.support, n < M) :
    ‖lp.finsuppL2 d-volterraPreconditionedL2 K (lp.finsuppL2 c)‖ =
      Real.sqrt (∑ i ∈ Finset.range (max M (N+K.totalDegree)),
        (d i-(-1 : ℝ)^i*((i : ℝ)+1)*volterraProriolCoefficients K c i)^2) := by
  rw [norm_eq_finite_sum _ _ (volterraFiniteResidual_cutoff K c d N M hc hd)]
  simp only [lp.coeFn_sub,Pi.sub_apply,lp.finsuppL2_apply,volterraPreconditionedL2_finsupp_apply]

/-- Every retained raw output row is a row of the diagonally rescaled rectangular Proriol matrix. -/
theorem volterraPreconditionedL2_rectangular_mulVec (K : MvPolynomial (Fin 2) ℝ)
    (N : ℕ) (v : Fin N → ℝ) (i : Fin (N+K.totalDegree)) :
    volterraPreconditionedL2 K (lp.finsuppL2 (∑ j : Fin N, Finsupp.single j.val (v j))) i.val =
      (-1 : ℝ)^i.val*((i.val : ℝ)+1)*(volterraProriolSection K N).mulVec v i := by
  rw [volterraPreconditionedL2_finsupp_apply,volterraProriolSection_mulVec]
end MvPolynomial
