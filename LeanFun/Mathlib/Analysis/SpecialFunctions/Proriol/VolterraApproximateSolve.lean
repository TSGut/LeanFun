/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraWeightedSolve
public import LeanFun.Mathlib.Analysis.InnerProductSpace.ApproximateCoerciveSection

/-! # Polynomial first-kind solves with approximated kernels and data

Reference: Gutleb's thesis, §2.7, Theorem 2.5 and Lemma 2.5.
Operator-norm consistency is measured after first-kind preconditioning.
-/

@[expose] public noncomputable section
open ContinuousLinearMap Polynomial Set Filter
open scoped Topology InnerProductSpace
namespace MvPolynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2

private theorem reflection_square {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (P : E →L[ℝ] E) (hP : P*P=P) :
    (1-2*P)*(1-2*P) = 1 := by noncomm_ring [hP]

private theorem positive_inverse_bound (K : MvPolynomial (Fin 2) ℝ)
    {a : ℝ} (ha : 0 < a) (hK : ∀ x ∈ Icc (0 : ℝ) 1, a ≤ eval (fun _ ↦ x) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
        (volterraPreconditionedL2 K))‖ ≤ C := by
  let A := lp.laurentToeplitz (volterraDiagonalLaurentSymbol K)
  have hb (u : H) : min a 1*‖u‖^2 ≤ RCLike.re ⟪u, A u⟫_ℝ :=
    (mul_le_mul_of_nonneg_right (min_le_left a 1) (sq_nonneg ‖u‖)).trans
      (inner_volterraDiagonalToeplitz_le K hK u)
  have he : A+(volterraPreconditionedL2 K-A) = volterraPreconditionedL2 K := by abel
  have hu := isUnit_volterraPreconditionedL2_of_pos K ha hK
  rw [← he] at hu
  have ht := lp.eventually_norm_inverse_coerciveFiniteSection_add_compact_le A
    (volterraPreconditionedL2 K-A) (lt_min ha zero_lt_one) (min_le_right a 1) hb
    (isCompactOperator_volterraPreconditionedL2_sub_symbol K) hu
  rw [he] at ht
  exact ⟨_,by positivity,ht⟩

/-- Polynomial first-kind sections have a uniform eventual inverse bound, for either sign. -/
private theorem exists_eventually_stable_volterraPreconditionedL2_ringInverse
    (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      IsUnit (coerciveFiniteSection (lp.initialL2Projection N) (volterraPreconditionedL2 K)) ∧
      ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N)
        (volterraPreconditionedL2 K))‖ ≤ C := by
  have hi := eventually_isUnit_volterraPreconditionedL2_section_of_nonvanishing K hd
  obtain ⟨a,ha,hp|hn⟩ := exists_pos_volterra_diagonal_bound_or_neg K hd
  · obtain ⟨C,hC,hb⟩ := positive_inverse_bound K ha hp
    exact ⟨C,hC,hi.and hb⟩
  · obtain ⟨C,hC,hb⟩ := positive_inverse_bound (-K) ha
      (fun x hx ↦ by simpa only [map_neg] using hn x hx)
    refine ⟨C*3,by positivity,?_⟩
    filter_upwards [hi,hb] with N hiN hbN
    refine ⟨hiN,?_⟩
    let P := lp.initialL2Projection (𝕜 := ℝ) N
    let Q : H →L[ℝ] H := 1-2*P
    have hP : P*P=P := lp.initialL2Projection_idempotent N
    have hQQ : Q*Q=1 := reflection_square P hP
    have hQ : IsUnit Q := isUnit_iff_exists.mpr ⟨Q,hQQ,hQQ⟩
    have hQi : Ring.inverse Q = Q := by
      calc
        _ = Ring.inverse Q * (Q*Q) := by rw [hQQ,mul_one]
        _ = Q := Ring.inverse_mul_cancel_left _ _ hQ
    have hnQ : ‖Q‖ ≤ 3 := by
      have heQ : Q = 1-P-P := by dsimp [Q]; noncomm_ring
      rw [heQ]
      have h1 := norm_sub_le (1 : H →L[ℝ] H) P
      have h2 := norm_sub_le (1-P) P
      have hpn := lp.norm_initialL2Projection_le (𝕜 := ℝ) N
      have hon := norm_id_le (𝕜 := ℝ) (E := H)
      change ‖P‖ ≤ 1 at hpn
      change ‖(1 : H →L[ℝ] H)‖ ≤ 1 at hon
      linarith
    have hs := coerciveFiniteSection_neg P (-volterraPreconditionedL2 K) hP
    rw [neg_neg] at hs
    rw [hs, Ring.inverse_mul (Or.inl hQ), hQi]
    rw [volterraPreconditionedL2_neg] at hbN
    exact (norm_mul_le _ _).trans (mul_le_mul hbN hnQ (norm_nonneg _) hC)


/-- Polynomial first-kind stability supplies genuine inverse values eventually. -/
theorem exists_eventually_stable_volterraPreconditionedL2
    (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      ∃ hN : IsUnit (volterraWeightedSection K N),
      ‖Ring.inverseAt (volterraWeightedSection K) ⟨N, hN⟩‖ ≤ C := by
  obtain ⟨C, hC, hs⟩ := exists_eventually_stable_volterraPreconditionedL2_ringInverse K hd
  refine ⟨C, hC, ?_⟩
  filter_upwards [hs] with N hN
  have hu : IsUnit (volterraWeightedSection K N) := hN.1
  refine ⟨hu, ?_⟩
  rw [Ring.inverseAt_eq_ringInverse]
  exact hN.2

/-- Small kernel changes preserve invertibility of the preconditioned operator. -/
theorem isUnit_volterraPreconditionedL2_of_near (K L : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (he : ‖Ring.inverseAt volterraPreconditionedL2 ⟨K, isUnit_volterraPreconditionedL2 K hd⟩‖ *
      ‖volterraPreconditionedL2 K-volterraPreconditionedL2 L‖ < 1) :
    IsUnit (volterraPreconditionedL2 L) := by
  apply isUnit_of_inverse_norm_mul_sub_lt_one _ _ (isUnit_volterraPreconditionedL2 K hd)
  simpa only [Ring.inverseAt_eq_ringInverse, volterraWeightedSection] using he

/-- Approximate kernels inherit eventual stability, with inverse existence included. -/
theorem eventually_stable_approximateVolterraWeightedSection
    (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (L : ℕ → MvPolynomial (Fin 2) ℝ)
    (hL : Tendsto (fun N ↦ volterraPreconditionedL2 (L N)) atTop
      (𝓝 (volterraPreconditionedL2 K))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      ∃ hN : IsUnit (volterraWeightedSection (L N) N),
      ‖Ring.inverseAt (fun N ↦ volterraWeightedSection (L N) N) ⟨N, hN⟩‖ ≤ C := by
  obtain ⟨C,hC,hA⟩ := exists_eventually_stable_volterraPreconditionedL2_ringInverse K hd
  refine ⟨2*C, by positivity, ?_⟩
  filter_upwards [lp.eventually_stable_approximateCoerciveFiniteSection _ _ hL hA] with N hN
  refine ⟨hN.1, ?_⟩
  simpa only [Ring.inverseAt_eq_ringInverse, volterraWeightedSection] using hN.2

/-- Approximate finite solves have a nontrivial cofinal index domain. -/
theorem approximateVolterraWeightedSolution_filter_neBot (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (L : ℕ → MvPolynomial (Fin 2) ℝ)
    (hL : Tendsto (fun N ↦ volterraPreconditionedL2 (L N)) atTop
      (𝓝 (volterraPreconditionedL2 K))) :
    NeBot (Ring.invertibleIndexFilter (fun N ↦ volterraWeightedSection (L N) N) atTop) := by
  obtain ⟨C, hC, hs⟩ := eventually_stable_approximateVolterraWeightedSection K hd L hL
  exact Ring.invertibleIndexFilter_neBot _ _ (hs.mono (fun _ h ↦ h.choose))

/-- Kernel, weighted-data, and section refinement converge on invertible cutoffs. -/
theorem tendsto_approximateVolterraWeightedSolution (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (L : ℕ → MvPolynomial (Fin 2) ℝ)
    (hL : Tendsto (fun N ↦ volterraPreconditionedL2 (L N)) atTop
      (𝓝 (volterraPreconditionedL2 K)))
    (q : ℕ → lp.FirstOrderL2) (r : lp.FirstOrderL2)
    (hq : Tendsto q atTop (𝓝 r)) :
    Tendsto (fun N : Ring.InvertibleIndex (fun N ↦ volterraWeightedSection (L N) N) ↦
      volterraWeightedFiniteSolution (L N) ⟨N.val, N.property⟩ (q N))
      (Ring.invertibleIndexFilter (fun N ↦ volterraWeightedSection (L N) N) atTop)
      (𝓝 (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r)) := by
  obtain ⟨C,_hC,hA⟩ := exists_eventually_stable_volterraPreconditionedL2_ringInverse K hd
  have he : volterraPreconditionedL2 K
      (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r) =
      volterraJacobiL2Equiv.symm r := by
    apply volterraJacobiL2Equiv.injective
    exact (volterraWeightedSolution_spec K hd r).trans
      (volterraJacobiL2Equiv.apply_symm_apply r).symm
  have hraw := lp.tendsto_approximateCoerciveFiniteSection_solution _ _ hL hA
    (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r)
    (fun N ↦ volterraJacobiL2Equiv.symm (q N))
    (by rw [he]; exact (volterraJacobiL2Equiv.symm.continuous.tendsto r).comp hq)
  have h := hraw.comp (Filter.tendsto_comap : Tendsto
    (Subtype.val : Ring.InvertibleIndex (fun N ↦ volterraWeightedSection (L N) N) → ℕ)
    (Filter.comap Subtype.val atTop) atTop)
  simpa only [Ring.invertibleIndexFilter, Function.comp_def,
    volterraWeightedFiniteSolution_eq_ringInverse] using h

/-- An invertible operator limit makes the full-solve index domain cofinal. -/
theorem volterraWeightedOperatorLimit_filter_neBot
    (L : ℕ → MvPolynomial (Fin 2) ℝ) (A : H →L[ℝ] H) (hA : IsUnit A)
    (hL : Tendsto (fun N ↦ volterraPreconditionedL2 (L N)) atTop (𝓝 A)) :
    NeBot (Ring.invertibleIndexFilter (fun N ↦ volterraPreconditionedL2 (L N)) atTop) :=
  Ring.invertibleIndexFilter_neBot _ _ (eventually_isUnit_of_tendsto hL hA)

/-- Full weighted solves converge to an invertible operator-norm limit on their genuine domain. -/
theorem tendsto_volterraWeightedSolution_of_operator_limit
    (L : ℕ → MvPolynomial (Fin 2) ℝ) (A : H →L[ℝ] H) (hA : IsUnit A)
    (hL : Tendsto (fun N ↦ volterraPreconditionedL2 (L N)) atTop (𝓝 A))
    (q : ℕ → lp.FirstOrderL2) (r : lp.FirstOrderL2) (hq : Tendsto q atTop (𝓝 r)) :
    Tendsto (fun N : Ring.InvertibleIndex (fun N ↦ volterraPreconditionedL2 (L N)) ↦
      volterraWeightedSolution ⟨L N, N.property⟩ (q N))
      (Ring.invertibleIndexFilter (fun N ↦ volterraPreconditionedL2 (L N)) atTop)
      (𝓝 ((↑(hA.unit⁻¹) : H →L[ℝ] H) (volterraJacobiL2Equiv.symm r))) := by
  have hc : Continuous (fun p : (H →L[ℝ] H) × H ↦ p.1 p.2) := by fun_prop
  have hi := Ring.tendsto_inverseAt hA.unit (by simpa only [IsUnit.unit_spec] using hL)
  have hq' := ((volterraJacobiL2Equiv.symm.continuous.tendsto r).comp hq).comp
    (Filter.tendsto_comap : Tendsto
      (Subtype.val : Ring.InvertibleIndex (fun N ↦ volterraPreconditionedL2 (L N)) → ℕ)
      (Filter.comap Subtype.val atTop) atTop)
  simpa only [Function.comp_def, volterraWeightedSolution, Ring.inverseAt_eq_ringInverse, volterraWeightedSection] using
    hc.continuousAt.tendsto.comp (hi.prodMk_nhds hq')

/-- Combined truncation, weighted-data, and kernel error at an invertible finite section. -/
theorem norm_approximateVolterraWeightedSolution_error_le
    (K L : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (N : Ring.InvertibleIndex (volterraWeightedSection L))
    (q r : lp.FirstOrderL2) :
    ‖volterraWeightedFiniteSolution L N q-
      volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r‖ ≤
      ‖Ring.inverseAt (volterraWeightedSection L) N‖ *
      ((1+‖volterraPreconditionedL2 K‖) *
        ‖lp.initialL2Projection N (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r)-
          volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r‖
        + ‖q-r‖ + ‖volterraPreconditionedL2 K-volterraPreconditionedL2 L‖ *
          ‖volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r‖) := by
  have he : volterraPreconditionedL2 K
      (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r) =
      volterraJacobiL2Equiv.symm r := by
    apply volterraJacobiL2Equiv.injective
    exact (volterraWeightedSolution_spec K hd r).trans
      (volterraJacobiL2Equiv.apply_symm_apply r).symm
  have h := lp.norm_approximateCoerciveFiniteSection_error_le
    (volterraPreconditionedL2 K) (volterraPreconditionedL2 L) N
    (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r)
    (volterraJacobiL2Equiv.symm q) N.property
  rw [he, ← map_sub, volterraJacobiL2Equiv.symm.norm_map] at h
  simpa only [volterraWeightedFiniteSolution_eq_ringInverse, Ring.inverseAt_eq_ringInverse, volterraWeightedSection] using h

/-- Synthesized inputs converge through the same invertible-section domain. -/
theorem tendsto_approximateVolterraWeightedSolution_synthesis
    (K : MvPolynomial (Fin 2) ℝ)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0)
    (L : ℕ → MvPolynomial (Fin 2) ℝ)
    (hL : Tendsto (fun N ↦ volterraPreconditionedL2 (L N)) atTop
      (𝓝 (volterraPreconditionedL2 K)))
    (q : ℕ → lp.FirstOrderL2) (r : lp.FirstOrderL2) (hq : Tendsto q atTop (𝓝 r)) :
    Tendsto (fun N : Ring.InvertibleIndex (fun N ↦ volterraWeightedSection (L N) N) ↦
      shiftedJacobiOneZeroSynthesis (volterraWeightedFiniteSolution (L N) ⟨N.val, N.property⟩ (q N)))
      (Ring.invertibleIndexFilter (fun N ↦ volterraWeightedSection (L N) N) atTop)
      (𝓝 (shiftedJacobiOneZeroSynthesis
        (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r))) :=
  (shiftedJacobiOneZeroSynthesis.continuous.tendsto _).comp
    (tendsto_approximateVolterraWeightedSolution K hd L hL q r hq)

/-- Full weighted solutions are stable under kernel and data perturbations. -/
theorem norm_volterraWeightedSolution_sub_le (K : MvPolynomial (Fin 2) ℝ)
    (L : Ring.InvertibleIndex volterraPreconditionedL2)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, eval (fun _ ↦ x) K ≠ 0) (q r : lp.FirstOrderL2) :
    ‖volterraWeightedSolution L q-volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r‖ ≤
      ‖Ring.inverseAt volterraPreconditionedL2 L‖ *
        (‖q-r‖ + ‖volterraPreconditionedL2 K-volterraPreconditionedL2 L‖ *
          ‖volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r‖) := by
  have he : volterraPreconditionedL2 K
      (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r) =
      volterraJacobiL2Equiv.symm r := by
    apply volterraJacobiL2Equiv.injective
    exact (volterraWeightedSolution_spec K hd r).trans
      (volterraJacobiL2Equiv.apply_symm_apply r).symm
  have h := norm_inverse_solution_sub_le (volterraPreconditionedL2 K)
    (volterraPreconditionedL2 L) L.property
    (volterraWeightedSolution ⟨K, isUnit_volterraPreconditionedL2 K hd⟩ r)
    (volterraJacobiL2Equiv.symm q)
  rw [he, ← map_sub, volterraJacobiL2Equiv.symm.norm_map] at h
  simpa only [volterraWeightedSolution_eq_ringInverse, Ring.inverseAt_eq_ringInverse, volterraWeightedSection] using h

end MvPolynomial
