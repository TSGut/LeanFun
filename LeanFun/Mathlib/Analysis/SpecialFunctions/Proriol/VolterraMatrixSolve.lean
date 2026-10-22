/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraMatrix

/-! # Convergent finite Proriol solves for continuous Volterra kernels

Polynomial kernels may change with the section size. Their actual assembled
matrices have unique solutions eventually, and zero-extended solutions converge
with separate solution-tail and kernel-error terms.
Reference: Gutleb–Olver, arXiv:1906.03907, §3.
-/

@[expose] public noncomputable section
open Polynomial Real Set Filter ContinuousLinearMap
open scoped Topology Matrix
namespace MvPolynomial

variable {K : (Fin 2 → ℝ) → ℝ} (hK : ContinuousOn K volterraTriangle)
  {M : ℝ} (hM : 0 ≤ M) (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M)
  (p : ℕ → MvPolynomial (Fin 2) ℝ) {B e : ℕ → ℝ}
  (hB : ∀ n, 0 ≤ B n) (bp : ∀ n z, z ∈ volterraTriangle → |eval z (p n)| ≤ B n)
  (he : ∀ n, 0 ≤ e n)
  (err : ∀ n z, z ∈ volterraTriangle → |eval z (p n) - K z| ≤ e n)
  (hte : Tendsto e atTop (𝓝 0))

include hK hM bK hB bp he err hte in
/-- Eventually every approximating assembled matrix has a unique finite solution. -/
theorem eventually_existsUnique_approximateProriolMatrix_solution :
    ∀ᶠ n in atTop, ∀ f : lp (fun _ : ℕ ↦ ℝ) 2,
      ∃! v : Fin n → ℝ, (1 - volterraProriolMatrix (p n) n) *ᵥ v = (fun i : Fin n ↦ f i) := by
  filter_upwards [eventually_existsUnique_approximateVolterra_solution hK hM bK
    (fun n ↦ (p n).continuous_eval.continuousOn) hB bp he err hte] with n hn f
  rw [volterraProriolMatrix_eq (p n) n (hB n) (bp n)]
  exact lp.existsUnique_initialL2Matrix_solution _ n f (hn f)

/-- Finite coordinates of the classical lifted solution at an invertible cutoff. -/
def volterraProriolMatrixSolution (f : lp (fun _ : ℕ ↦ ℝ) 2)
    (n : Ring.InvertibleIndex (approximateVolterraCoefficientSection
      (fun n ↦ (p n).continuous_eval.continuousOn) hB bp)) : Fin n.val → ℝ :=
  fun i ↦ Ring.inverseAt (approximateVolterraCoefficientSection
    (fun n ↦ (p n).continuous_eval.continuousOn) hB bp) n
      (lp.initialL2Projection n.val f) i

/-- At every invertible cutoff, zero extension recovers the lifted solution
and the finite coordinates solve the assembled matrix equation. -/
theorem volterraProriolMatrixSolution_spec
    (n : Ring.InvertibleIndex (approximateVolterraCoefficientSection
      (fun n ↦ (p n).continuous_eval.continuousOn) hB bp))
    (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    lp.initialL2Vector (volterraProriolMatrixSolution p hB bp f n) =
      Ring.inverseAt (approximateVolterraCoefficientSection
        (fun n ↦ (p n).continuous_eval.continuousOn) hB bp) n
        (lp.initialL2Projection n.val f) ∧
    (1 - volterraProriolMatrix (p n.val) n.val) *ᵥ
      volterraProriolMatrixSolution p hB bp f n = (fun i : Fin n.val ↦ f i) := by
  have hs := liftedFiniteSection_solution_mem (lp.initialL2Projection n.val)
    (-volterraL2CoefficientOperator (p n.val).continuous_eval.continuousOn
      (hB n.val) (bp n.val)) (lp.initialL2Projection_idempotent n.val)
    (by simpa only [approximateVolterraCoefficientSection, volterraCoefficientSection]
      using n.property) f
  have hv : lp.initialL2Vector (volterraProriolMatrixSolution p hB bp f n) =
      Ring.inverseAt (approximateVolterraCoefficientSection
        (fun n ↦ (p n).continuous_eval.continuousOn) hB bp) n
        (lp.initialL2Projection n.val f) := by
    unfold volterraProriolMatrixSolution
    rw [lp.initialL2Vector_restrict, Ring.inverseAt_eq_ringInverse]
    exact hs.1
  refine ⟨hv, (volterraProriolMatrix_equation_iff (p n.val) (hB n.val) (bp n.val) _ f).mpr ?_⟩
  rw [hv, Ring.inverseAt_eq_ringInverse]
  simpa only [approximateVolterraCoefficientSection, volterraCoefficientSection,
    sub_eq_add_neg, add_apply, one_apply_eq_self, _root_.neg_apply] using hs.2

include hK hM bK he err hte in
/-- All sufficiently large cutoffs admit classical assembled solves. -/
theorem eventually_volterraProriolMatrixSolution_spec :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (approximateVolterraCoefficientSection
      (fun n ↦ (p n).continuous_eval.continuousOn) hB bp n),
      ∀ f : lp (fun _ : ℕ ↦ ℝ) 2,
      lp.initialL2Vector (volterraProriolMatrixSolution p hB bp f ⟨n, hn⟩) =
        Ring.inverseAt (approximateVolterraCoefficientSection
          (fun n ↦ (p n).continuous_eval.continuousOn) hB bp) ⟨n, hn⟩
          (lp.initialL2Projection n f) ∧
      (1 - volterraProriolMatrix (p n) n) *ᵥ
        volterraProriolMatrixSolution p hB bp f ⟨n, hn⟩ = (fun i : Fin n ↦ f i) := by
  filter_upwards [eventually_stable_approximateVolterraSection hK hM bK
    (fun n ↦ (p n).continuous_eval.continuousOn) hB bp he err hte] with n hn
  obtain ⟨hn, _⟩ := hn
  exact ⟨hn, fun f ↦ volterraProriolMatrixSolution_spec p hB bp ⟨n, hn⟩ f⟩

include he err hte in
/-- Zero-extended classical finite solutions converge through invertible cutoffs. -/
theorem tendsto_volterraProriolMatrixSolution (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    Tendsto (fun n : Ring.InvertibleIndex (approximateVolterraCoefficientSection
      (fun n ↦ (p n).continuous_eval.continuousOn) hB bp) ↦
      lp.initialL2Vector (volterraProriolMatrixSolution p hB bp f n))
      (Ring.invertibleIndexFilter (approximateVolterraCoefficientSection
        (fun n ↦ (p n).continuous_eval.continuousOn) hB bp) atTop)
      (𝓝 (volterraCoefficientInverse hK hM bK f)) := by
  apply (tendsto_approximateVolterra_solution hK hM bK
    (fun n ↦ (p n).continuous_eval.continuousOn) hB bp he err hte f).congr'
  exact Filter.Eventually.of_forall (fun n ↦ (volterraProriolMatrixSolution_spec p hB bp n f).1.symm)

include he err hte in
/-- Combined finite matrix error: coefficient tail plus uniform kernel error. -/
theorem eventually_norm_volterraProriolMatrixSolution_error_le :
    ∀ᶠ n in atTop, ∃ hn : IsUnit (approximateVolterraCoefficientSection
      (fun n ↦ (p n).continuous_eval.continuousOn) hB bp n),
      ∀ u : lp (fun _ : ℕ ↦ ℝ) 2,
      ‖lp.initialL2Vector (volterraProriolMatrixSolution p hB bp
        (u - volterraL2CoefficientOperator hK hM bK u) ⟨n, hn⟩) - u‖ ≤
        (‖volterraCoefficientInverse hK hM bK‖ + 1) *
          (‖lp.initialL2Projection n u - u‖ + e n * ‖u‖) := by
  filter_upwards [eventually_norm_approximateVolterra_error_le hK hM bK
    (fun n ↦ (p n).continuous_eval.continuousOn) hB bp he err hte] with n hn
  obtain ⟨hn, heN⟩ := hn
  refine ⟨hn, fun u ↦ ?_⟩
  rw [(volterraProriolMatrixSolution_spec p hB bp ⟨n, hn⟩ _).1]
  exact heN u

/-- Every continuous kernel admits a sequence of bounded polynomial kernels
with a certified vanishing uniform error on the Volterra triangle. -/
theorem exists_volterraPolynomialKernel_sequence :
    ∃ (q : ℕ → MvPolynomial (Fin 2) ℝ) (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
      (bq : ∀ n z, z ∈ volterraTriangle → |eval z (q n)| ≤ C n),
      (∀ n z, z ∈ volterraTriangle → |eval z (q n) - K z| ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ f : lp (fun _ : ℕ ↦ ℝ) 2,
        Tendsto (fun n : Ring.InvertibleIndex (approximateVolterraCoefficientSection
          (fun n ↦ (q n).continuous_eval.continuousOn) hC bq) ↦
          lp.initialL2Vector (volterraProriolMatrixSolution q hC bq f n))
          (Ring.invertibleIndexFilter (approximateVolterraCoefficientSection
            (fun n ↦ (q n).continuous_eval.continuousOn) hC bq) atTop)
          (𝓝 (volterraCoefficientInverse hK hM bK f))) := by
  have hp : ∀ n : ℕ, ∃ q : MvPolynomial (Fin 2) ℝ,
      ∀ z ∈ volterraTriangle, |eval z q - K z| < 1 / ((n : ℝ) + 1) :=
    fun n ↦ exists_polynomial_near_volterraKernel hK (by positivity)
  choose q hq using hp
  have hC : ∀ n : ℕ, 0 ≤ M + 1 / ((n : ℝ) + 1) := fun n ↦ by positivity
  have bq : ∀ n z, z ∈ volterraTriangle → |eval z (q n)| ≤ M + 1 / ((n : ℝ) + 1) := by
    intro n z hz
    calc
      _ ≤ |eval z (q n) - K z| + |K z| := by
        simpa only [sub_add_cancel] using abs_add_le (eval z (q n) - K z) (K z)
      _ ≤ 1 / ((n : ℝ) + 1) + M := add_le_add (hq n z hz).le (bK z hz)
      _ = _ := add_comm _ _
  refine ⟨q, _, hC, bq, (fun n z hz ↦ (hq n z hz).le), fun f ↦ ?_⟩
  exact tendsto_volterraProriolMatrixSolution hK hM bK q hC bq
    (fun n ↦ by positivity) (fun n z hz ↦ (hq n z hz).le)
    tendsto_one_div_add_atTop_nhds_zero_nat f

end MvPolynomial
