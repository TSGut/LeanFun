/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.InnerProduct
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.MvPolynomial

/-! # Multivariate polynomial evaluation in L²
Finite moments give a linear evaluation map to L² and the expected integral
pairing. Reference: Dunkl–Xu, Chapter 3.
-/

public section
namespace MvPolynomial
open MeasureTheory
open scoped InnerProductSpace
variable {σ : Type*} [Fintype σ] {μ : Measure (σ → ℝ)} (hμ : HasFiniteMoments μ)
include hμ

/-- Finite polynomial moments put every polynomial in L² (Dunkl–Xu, Chapter 3). -/
theorem memLp_eval_of_hasFiniteMoments (p : MvPolynomial σ ℝ) : MemLp (fun x ↦ eval x p) 2 μ := by
  exact (memLp_two_iff_integrable_sq (p.continuous_eval.aestronglyMeasurable)).mpr (hμ p)

/-- Polynomial evaluation as a linear map to weighted L² (Dunkl–Xu, Chapter 3). -/
noncomputable def polynomialToL2 : MvPolynomial σ ℝ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun p := (memLp_eval_of_hasFiniteMoments hμ p).toLp (fun x ↦ eval x p)
  map_add' p q := by
    apply Lp.ext
    filter_upwards [(memLp_eval_of_hasFiniteMoments hμ (p + q)).coeFn_toLp,
      (memLp_eval_of_hasFiniteMoments hμ p).coeFn_toLp, (memLp_eval_of_hasFiniteMoments hμ q).coeFn_toLp,
      Lp.coeFn_add ((memLp_eval_of_hasFiniteMoments hμ p).toLp _) ((memLp_eval_of_hasFiniteMoments hμ q).toLp _)]
      with x hpq hp hq hadd
    rw [hpq, hadd]
    simp only [Pi.add_apply, hp, hq, eval_add]
  map_smul' c p := by
    change (memLp_eval_of_hasFiniteMoments hμ (c • p)).toLp _ = c • (memLp_eval_of_hasFiniteMoments hμ p).toLp _
    apply Lp.ext
    filter_upwards [(memLp_eval_of_hasFiniteMoments hμ (c • p)).coeFn_toLp,
      (memLp_eval_of_hasFiniteMoments hμ p).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_eval_of_hasFiniteMoments hμ p).toLp _)] with x hcp hp hsmul
    rw [hcp, hsmul]
    simp only [Pi.smul_apply, hp, smul_eq_C_mul, map_mul, eval_C, smul_eq_mul]

/-- An almost-everywhere representative of polynomial evaluation (Dunkl–Xu, Chapter 3). -/
theorem coe_polynomialToL2 (p : MvPolynomial σ ℝ) : polynomialToL2 hμ p =ᵐ[μ] fun x ↦ eval x p :=
  (memLp_eval_of_hasFiniteMoments hμ p).coeFn_toLp

/-- The polynomial L² inner product is the weighted product integral (Dunkl–Xu, Chapter 3). -/
theorem inner_polynomialToL2 (p q : MvPolynomial σ ℝ) :
    ⟪polynomialToL2 hμ p, polynomialToL2 hμ q⟫_ℝ = ∫ x, eval x p * eval x q ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_polynomialToL2 hμ p, coe_polynomialToL2 hμ q] with x hp hq
  simp [hp, hq, mul_comm]

end MvPolynomial
