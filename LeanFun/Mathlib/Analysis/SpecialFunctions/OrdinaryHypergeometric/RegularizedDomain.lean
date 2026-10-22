/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.Domain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-! # Classical regularized hypergeometric series
Coefficients use the entire reciprocal Gamma function. Values exist exactly on
the natural-order convergence domain. References: DLMF 15.2.2 and 16.2.
-/
@[expose] public noncomputable section
open Polynomial Filter
open scoped Topology
namespace Complex

/-- Entire reciprocal Gamma supplies classical coefficients even at its zeros. -/
def regularizedHGFunCoeffOn (a b : Multiset ℂ) (n : ℕ) : ℂ :=
  (a.map (ascPochhammer ℂ n).eval).prod *
    (b.map (fun c ↦ reciprocalGamma (c + n))).prod / (n.factorial : ℂ)


/-- The regularized Gauss coefficients in their classical form. -/
theorem regularizedHGFunCoeffOn_gauss (a b c : ℂ) (n : ℕ) :
    regularizedHGFunCoeffOn {a, b} {c} n =
      (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b *
        reciprocalGamma (c + n) / (n.factorial : ℂ) := by
  simp [regularizedHGFunCoeffOn]

/-- The exact natural-order convergence domain of a regularized series. -/
abbrev RegularizedHGSeriesPoint (a b : Multiset ℂ) :=
  {z : ℂ // ∃ s : ℂ, Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
    regularizedHGFunCoeffOn a b n * z ^ n) atTop (𝓝 s)}

/-- A regularized hypergeometric value only where its defining series converges. -/
def regularizedHGFunOn (a b : Multiset ℂ) (z : RegularizedHGSeriesPoint a b) : ℂ :=
  z.property.choose

/-- Natural partial sums converge to the classical regularized value. -/
theorem tendsto_regularizedHGFunOn (a b : Multiset ℂ)
    (z : RegularizedHGSeriesPoint a b) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
      regularizedHGFunCoeffOn a b n * z.val ^ n) atTop (𝓝 (regularizedHGFunOn a b z)) :=
  z.property.choose_spec

/-- Uniqueness of the naturally ordered regularized sum. -/
theorem regularizedHGFunOn_eq_of_tendsto (a b : Multiset ℂ)
    (z : RegularizedHGSeriesPoint a b) {s : ℂ}
    (hs : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
      regularizedHGFunCoeffOn a b n * z.val ^ n) atTop (𝓝 s)) :
    regularizedHGFunOn a b z = s :=
  tendsto_nhds_unique (tendsto_regularizedHGFunOn a b z) hs

/-- Unconditional convergence supplies a natural-order convergence point. -/
def RegularizedHGSeriesPoint.ofHasSum (a b : Multiset ℂ) {z s : ℂ}
    (hs : HasSum (fun n ↦ regularizedHGFunCoeffOn a b n * z ^ n) s) :
    RegularizedHGSeriesPoint a b := ⟨z, s, hs.tendsto_sum_nat⟩

/-- The supplied sum agrees with the classical value. -/
theorem regularizedHGFunOn_ofHasSum (a b : Multiset ℂ) {z s : ℂ}
    (hs : HasSum (fun n ↦ regularizedHGFunCoeffOn a b n * z ^ n) s) :
    regularizedHGFunOn a b (.ofHasSum a b hs) = s :=
  regularizedHGFunOn_eq_of_tendsto a b _ hs.tendsto_sum_nat

/-- The regularized Gauss specialization on its classical series domain. -/
abbrev regularizedGaussHGFunOn (a b c : ℂ)
    (z : RegularizedHGSeriesPoint {a, b} {c}) : ℂ := regularizedHGFunOn {a, b} {c} z

end Complex

namespace Complex
/-- Ordinary and regularized coefficients differ by the genuine Gamma factor. -/
theorem regularizedHGFunCoeffOn_eq_gauss_div_Gamma (a b : ℂ) (c : GammaPoint) (n : ℕ) :
    regularizedHGFunCoeffOn {a, b} {c.val} n =
      ordinaryHypergeometricCoefficientOn (.ofNoPole a b c.val c.property) n / GammaOn c := by
  classical
  have hcn : (ascPochhammer ℂ n).eval c.val ≠ 0 := by
    intro hz
    obtain ⟨k,_,hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp hz
    exact c.property k (by simpa using congrArg Neg.neg hk.symm)
  have hr : reciprocalGamma (c.val+n) = (GammaOn (c.addNat n))⁻¹ := by
    change reciprocalGamma (c.addNat n).val = _
    rw [reciprocalGamma, dite_eq_left (c.addNat n).property]
  rw [regularizedHGFunCoeffOn_gauss, hr,
    ordinaryHypergeometricCoefficientOn_eq_div _ n hcn]
  dsimp only [GaussParameters.ofNoPole]
  rw [← GammaOn_add_nat_div c n]
  have h0 := GammaOn_ne_zero c
  have hn := GammaOn_ne_zero (c.addNat n)
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/-- Any classically convergent ordinary series with a non-pole denominator also converges in regularized form. -/
def RegularizedHGSeriesPoint.ofGauss (a b : ℂ) (c : GammaPoint)
    (z : GaussSeriesPoint (GaussParameters.ofNoPole a b c.val c.property)) :
    RegularizedHGSeriesPoint {a, b} {c.val} := by
  refine ⟨z.val, ordinaryHypergeometricOn _ z / GammaOn c, ?_⟩
  have h := (tendsto_ordinaryHypergeometricOn _ z).div_const (GammaOn c)
  simpa only [regularizedHGFunCoeffOn_eq_gauss_div_Gamma,
    div_mul_eq_mul_div, Finset.sum_div] using h

/-- The normalisation identity on the full classical series domain, including conditional convergence. -/
theorem ordinaryHypergeometricOn_div_Gamma_eq (a b : ℂ) (c : GammaPoint)
    (z : GaussSeriesPoint (GaussParameters.ofNoPole a b c.val c.property)) :
    ordinaryHypergeometricOn _ z / GammaOn c =
      regularizedGaussHGFunOn a b c.val (.ofGauss a b c z) := by
  symm
  apply regularizedHGFunOn_eq_of_tendsto
  have h := (tendsto_ordinaryHypergeometricOn _ z).div_const (GammaOn c)
  simpa only [RegularizedHGSeriesPoint.ofGauss,
    regularizedHGFunCoeffOn_eq_gauss_div_Gamma, div_mul_eq_mul_div, Finset.sum_div] using h
end Complex
