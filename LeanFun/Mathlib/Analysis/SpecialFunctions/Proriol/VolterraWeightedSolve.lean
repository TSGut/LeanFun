/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraSignedSections
public import LeanFun.Mathlib.Analysis.Normed.Operator.SmallNormSolve

/-! # Polynomial first-kind Volterra solves with weighted data

The endpoint-factor-free output belongs to first-order weighted coefficient
space. Reference: Gutleb's thesis, §2.7; Gutleb–Olver, first-kind equations.
-/

@[expose] public noncomputable section
open ContinuousLinearMap Filter Polynomial Set
open scoped Topology
namespace MvPolynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2

/-- The polynomial first-kind map into its weighted coefficient range. -/
def volterraWeightedL2 (K : MvPolynomial (Fin 2) ℝ) : H →L[ℝ] lp.FirstOrderL2 :=
  volterraJacobiL2Equiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (volterraPreconditionedL2 K)

/-- The solution for weighted data on the invertible-kernel domain. -/
def volterraWeightedSolution
    (K : Ring.InvertibleIndex volterraPreconditionedL2) (q : lp.FirstOrderL2) : H :=
  Ring.inverseAt volterraPreconditionedL2 K (volterraJacobiL2Equiv.symm q)

/-- Internal bridge to imported inversion on its classical domain. -/
theorem volterraWeightedSolution_eq_ringInverse
    (K : Ring.InvertibleIndex volterraPreconditionedL2) (q : lp.FirstOrderL2) :
    volterraWeightedSolution K q =
      Ring.inverse (volterraPreconditionedL2 K) (volterraJacobiL2Equiv.symm q) := by
  simp only [volterraWeightedSolution, Ring.inverseAt_eq_ringInverse]

/-- The canonical weighted solution solves the equation for every invertible kernel. -/
theorem volterraWeightedSolution_property
    (K : Ring.InvertibleIndex volterraPreconditionedL2) (q : lp.FirstOrderL2) :
    volterraWeightedL2 K (volterraWeightedSolution K q) = q := by
  have h := congrArg (fun B : H →L[ℝ] H ↦ B (volterraJacobiL2Equiv.symm q))
    (Ring.inverseAt_mul volterraPreconditionedL2 K).2
  change volterraPreconditionedL2 K
    (Ring.inverseAt volterraPreconditionedL2 K (volterraJacobiL2Equiv.symm q)) =
      volterraJacobiL2Equiv.symm q at h
  change volterraJacobiL2Equiv (volterraPreconditionedL2 K
    (Ring.inverseAt volterraPreconditionedL2 K (volterraJacobiL2Equiv.symm q))) = q
  rw [h]
  exact volterraJacobiL2Equiv.apply_symm_apply q

/-- Nonvanishing diagonal gives a solution for every weighted right-hand side. -/
theorem volterraWeightedSolution_spec (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) (q : lp.FirstOrderL2) :
    volterraWeightedL2 K (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ q) = q := by
  have h := congrArg (fun B : H →L[ℝ] H ↦ B (volterraJacobiL2Equiv.symm q))
    (Ring.mul_inverse_cancel _ (isUnit_volterraPreconditionedL2 K hd))
  rw [volterraWeightedSolution_eq_ringInverse]
  change volterraJacobiL2Equiv
    (volterraPreconditionedL2 K (Ring.inverse (volterraPreconditionedL2 K)
      (volterraJacobiL2Equiv.symm q))) = q
  rw [show volterraPreconditionedL2 K (Ring.inverse (volterraPreconditionedL2 K)
    (volterraJacobiL2Equiv.symm q)) = volterraJacobiL2Equiv.symm q from h]
  exact volterraJacobiL2Equiv.apply_symm_apply q

/-- The weighted-data solution is unique in raw square-summable coefficients. -/
theorem existsUnique_volterraWeightedL2_solution (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) (q : lp.FirstOrderL2) :
    ∃! u : H, volterraWeightedL2 K u = q := by
  refine ⟨volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ q, volterraWeightedSolution_spec K hd q, ?_⟩
  intro v hv
  apply injective_volterraPreconditionedL2 K hd
  apply volterraJacobiL2Equiv.injective
  exact hv.trans (volterraWeightedSolution_spec K hd q).symm

/-- Full weighted residuals certify raw coefficient error. -/
theorem norm_volterraWeightedSolution_error_le (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (q : lp.FirstOrderL2) (v : H) :
    ‖v - volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ q‖ ≤
      ‖Ring.inverseAt volterraPreconditionedL2 ⟨K, isUnit_volterraPreconditionedL2 K hd⟩‖ * ‖volterraWeightedL2 K v - q‖ := by
  have h := norm_sub_inverse_apply_le_residual (volterraPreconditionedL2 K)
    (isUnit_volterraPreconditionedL2 K hd) (volterraJacobiL2Equiv.symm q) v
  have he : ‖volterraPreconditionedL2 K v - volterraJacobiL2Equiv.symm q‖ =
      ‖volterraWeightedL2 K v - q‖ := by
    rw [← volterraJacobiL2Equiv.norm_map, map_sub, volterraJacobiL2Equiv.apply_symm_apply]
    rfl
  simpa only [volterraWeightedSolution_eq_ringInverse, Ring.inverseAt_eq_ringInverse] using (he ▸ h)

/-- The identity-padded finite weighted section. -/
def volterraWeightedSection (K : MvPolynomial (Fin 2) ℝ) (N : ℕ) : H →L[ℝ] H :=
  coerciveFiniteSection (lp.initialL2Projection N) (volterraPreconditionedL2 K)

/-- A finite solve is defined only at an invertible section. -/
def volterraWeightedFiniteSolution (K : MvPolynomial (Fin 2) ℝ)
    (N : Ring.InvertibleIndex (volterraWeightedSection K))
    (q : lp.FirstOrderL2) : H :=
  (Ring.inverseAt (R := H →L[ℝ] H) (volterraWeightedSection K) N)
    (lp.initialL2Projection N.val (volterraJacobiL2Equiv.symm q))

/-- Internal bridge on the genuine finite-solve domain. -/
theorem volterraWeightedFiniteSolution_eq_ringInverse (K : MvPolynomial (Fin 2) ℝ)
    (N : Ring.InvertibleIndex (volterraWeightedSection K))
    (q : lp.FirstOrderL2) :
    volterraWeightedFiniteSolution K N q =
      Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
        (volterraPreconditionedL2 K)) (lp.initialL2Projection N (volterraJacobiL2Equiv.symm q)) := by
  simp only [volterraWeightedFiniteSolution, Ring.inverseAt_eq_ringInverse, volterraWeightedSection]

/-- The invertible finite-solve domain contains a tail and has a nontrivial limiting filter. -/
theorem volterraWeightedFiniteSolution_filter_neBot (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) :
    NeBot (Ring.invertibleIndexFilter (volterraWeightedSection K) atTop) :=
  Ring.invertibleIndexFilter_neBot _ _
    (eventually_isUnit_volterraPreconditionedL2_section_of_nonvanishing K hd)

/-- Finite solutions converge through the cofinal domain of invertible cutoffs. -/
theorem tendsto_volterraWeightedFiniteSolution (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) (q : lp.FirstOrderL2) :
    Tendsto (fun N ↦ volterraWeightedFiniteSolution K N q)
      (Ring.invertibleIndexFilter (volterraWeightedSection K) atTop)
      (𝓝 (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ q)) := by
  have h := (tendsto_volterraPreconditionedL2_section_solution_of_nonvanishing K hd
    (volterraJacobiL2Equiv.symm q)).comp
    (Filter.tendsto_comap : Tendsto
      (Subtype.val : Ring.InvertibleIndex (volterraWeightedSection K) → ℕ)
      (Filter.comap Subtype.val atTop) atTop)
  simpa only [Ring.invertibleIndexFilter, Function.comp_def,
    volterraWeightedFiniteSolution_eq_ringInverse, volterraWeightedSolution_eq_ringInverse] using h

/-- Synthesized inputs converge on the same cofinal cutoff domain. -/
theorem tendsto_volterraWeightedFiniteSolution_synthesis (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) (q : lp.FirstOrderL2) :
    Tendsto (fun N ↦ shiftedJacobiOneZeroSynthesis (volterraWeightedFiniteSolution K N q))
      (Ring.invertibleIndexFilter (volterraWeightedSection K) atTop)
      (𝓝 (shiftedJacobiOneZeroSynthesis
        (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ q))) :=
  (shiftedJacobiOneZeroSynthesis.continuous.tendsto _).comp
    (tendsto_volterraWeightedFiniteSolution K hd q)

/-- Weighted output coefficients agree with exact finite Proriol assembly. -/
theorem volterraWeightedL2_finsupp (K : MvPolynomial (Fin 2) ℝ)
    (c : ℕ →₀ ℝ) (i : ℕ) :
    (volterraWeightedL2 K (lp.finsuppL2 c)).1 i = volterraProriolCoefficients K c i := by
  have h := congrArg (fun u : H ↦ u i) (volterraRawDiagonal_preconditioned_finsupp K c)
  rw [volterraRawDiagonal_eq_weighted] at h
  exact h

private theorem projection_coord (N : ℕ) (u : H) (i : ℕ) :
    lp.initialL2Projection N u i = if i < N then u i else 0 := by
  simp only [lp.initialL2Projection_apply, lp.coeFn_sum, lp.coeFn_single,
    Finset.sum_apply, Finset.sum_pi_single, Finset.mem_range]

/-- An invertible finite section solves the resolved weighted equations and has zero tail. -/
theorem volterraWeightedFiniteSolution_equations (K : MvPolynomial (Fin 2) ℝ)
    (N : Ring.InvertibleIndex (volterraWeightedSection K))
    (q : lp.FirstOrderL2) :
    (∀ i, (N : ℕ) ≤ i → volterraWeightedFiniteSolution K N q i = 0) ∧
    (∀ i, i < (N : ℕ) → (volterraWeightedL2 K (volterraWeightedFiniteSolution K N q)).1 i =
      q.1 i) := by
  let u := volterraWeightedFiniteSolution K N q
  let P := lp.initialL2Projection (𝕜 := ℝ) N
  let A := volterraPreconditionedL2 K
  have he : u - P u + P (A (P u)) = P (volterraJacobiL2Equiv.symm q) := by
    simpa only [u, volterraWeightedFiniteSolution_eq_ringInverse, volterraWeightedSection,
      coerciveFiniteSection, mul_apply_eq_comp, add_apply, sub_apply, one_apply_eq_self, comp_apply, P, A] using
      congrArg (fun B : H →L[ℝ] H ↦ B (P (volterraJacobiL2Equiv.symm q)))
      (Ring.mul_inverse_cancel _ N.property)
  have ht : ∀ i, (N : ℕ) ≤ i → u i = 0 := by
    intro i hi
    have h := congrArg (fun v : H ↦ v i) he
    simpa only [lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
      P, projection_coord, ite_eq_right (not_lt.mpr hi), sub_zero, add_zero] using h
  have hp : P u = u := by
    apply lp.ext
    funext i
    change lp.initialL2Projection N u i = u i
    rw [projection_coord]
    split_ifs with hi
    · rfl
    · exact (ht i (le_of_not_gt hi)).symm
  refine ⟨ht, ?_⟩
  intro i hi
  rw [hp, sub_self, zero_add] at he
  have h := congrArg (fun v : H ↦ v i) he
  have hc : A u i = volterraJacobiL2Equiv.symm q i := by
    simpa only [P, projection_coord, ite_eq_left hi] using h
  change (volterraJacobiL2Equiv (A u)).1 i = q.1 i
  rw [volterraJacobiL2Equiv_apply, hc]
  simpa only [volterraJacobiL2Equiv_apply] using
    congrArg (fun v : lp.FirstOrderL2 ↦ v.1 i)
      (volterraJacobiL2Equiv.apply_symm_apply q)

/-- Resolved equations hold together with an invertibility certificate eventually. -/
theorem eventually_volterraWeightedFiniteSolution_equations (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) (q : lp.FirstOrderL2) :
    ∀ᶠ N in atTop, ∃ hN : IsUnit (volterraWeightedSection K N),
      (∀ i, N ≤ i → volterraWeightedFiniteSolution K ⟨N, hN⟩ q i = 0) ∧
      (∀ i, i < N → (volterraWeightedL2 K (volterraWeightedFiniteSolution K ⟨N, hN⟩ q)).1 i =
        q.1 i) := by
  filter_upwards [eventually_isUnit_volterraPreconditionedL2_section_of_nonvanishing K hd]
    with N hN
  change IsUnit (volterraWeightedSection K N) at hN
  exact ⟨hN, volterraWeightedFiniteSolution_equations K ⟨N, hN⟩ q⟩

/-- The finite Proriol equations are precisely the retained weighted operator equations. -/
theorem volterraProriolCoefficients_equations_iff (K : MvPolynomial (Fin 2) ℝ)
    (N : ℕ) (q : lp.FirstOrderL2) (c : ℕ →₀ ℝ) :
    (∀ i, i < N → volterraProriolCoefficients K c i = q.1 i) ↔
      (∀ i, i < N → (volterraWeightedL2 K (lp.finsuppL2 c)).1 i = q.1 i) := by
  simp only [volterraWeightedL2_finsupp]

/-- Weighted residuals also control the error of the synthesized physical input. -/
theorem norm_volterraWeightedSolution_synthesis_error_le (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (q : lp.FirstOrderL2) (v : H) :
    ‖shiftedJacobiOneZeroSynthesis v -
      shiftedJacobiOneZeroSynthesis (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ q)‖ ≤
      ‖shiftedJacobiOneZeroSynthesis‖ * (‖Ring.inverseAt volterraPreconditionedL2 ⟨K, isUnit_volterraPreconditionedL2 K hd⟩‖ *
        ‖volterraWeightedL2 K v - q‖) := by
  rw [← map_sub]
  exact (shiftedJacobiOneZeroSynthesis.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_volterraWeightedSolution_error_le K hd q v)
      (norm_nonneg _))

end MvPolynomial
