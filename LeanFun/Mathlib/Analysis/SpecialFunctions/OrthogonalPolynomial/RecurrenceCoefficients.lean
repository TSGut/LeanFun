/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Recurrence

/-!
# Explicit recurrence coefficients

We write `X Pₙ₊₁ = Aₙ₊₁ Pₙ₊₂ + Bₙ₊₁ Pₙ₊₁ + Cₙ Pₙ`.
The shifted index of `C` avoids an artificial negative-index polynomial.
References: DLMF 18.2(iv), https://dlmf.nist.gov/18.2#iv; Szegő, Chapter 3.
-/

@[expose] public section

open MeasureTheory

namespace Polynomial.Sequence

/-- Classical square-integrability data for one polynomial (DLMF 18.2.5). -/
structure IntegrableSquare (μ : Measure ℝ) (p : ℝ[X]) where
  integrable : Integrable (fun x ↦ p.eval x * p.eval x) μ

/-- Construct the square domain from available local integrability evidence. -/
abbrev IntegrableSquare.of (μ : Measure ℝ) (p : ℝ[X])
    (hi : Integrable (fun x ↦ p.eval x * p.eval x) μ := by
      first
      | solve_by_elim (maxDepth := 4) [Polynomial.HasFiniteMoments.integrable_mul, Polynomial.Sequence.IsOrthogonal.integrable]
      | exact (Polynomial.HasPositiveDefiniteIntegral.hasFiniteMoments (by assumption)).integrable_mul _ _
      | aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    IntegrableSquare μ p := ⟨hi⟩

/-- The bundled square has a classical finite integral. -/
theorem IntegrableSquare.integrable_square {μ : Measure ℝ} {p : ℝ[X]}
    (d : IntegrableSquare μ p) : Integrable (fun x ↦ p.eval x ^ 2) μ := by
  simpa only [pow_two] using d.integrable

/-- The squared integral norm on its classical input domain (DLMF 18.2.5). -/
noncomputable def squaredNorm (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (d : IntegrableSquare μ (P n)) : ℝ :=
  integralInner μ (IntegrablePair.of μ (P n) (P n) d.integrable)

/-- The classical squared-norm integral formula. -/
theorem squaredNorm_apply (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (d : IntegrableSquare μ (P n)) :
    P.squaredNorm μ n d = ∫ x, (P n).eval x ^ 2 ∂μ := by
  simp only [squaredNorm, integralInner_self]

/-- The forward coefficient in multiplication by `X` (DLMF 18.2(iv)). -/
noncomputable def recurrenceA (P : Sequence ℝ) (n : ℕ) : ℝ :=
  (P n).leadingCoeff / (P (n + 1)).leadingCoeff

/-- Squared norms are strictly positive under nondegeneracy (DLMF 18.2.5). -/
theorem squaredNorm_pos {μ : Measure ℝ} (hpos : HasPositiveDefiniteIntegral μ)
    (P : Sequence ℝ) (n : ℕ) : 0 < P.squaredNorm μ n (IntegrableSquare.of _ _) := by
  simpa [squaredNorm, integralInner_self] using hpos (P n) (P.ne_zero n)

/-- The local classical domain of the diagonal recurrence coefficient. -/
structure RecurrenceBInput (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) where
  square : IntegrableSquare μ (P n)
  mixed : Integrable (fun x ↦ (X * P n).eval x * (P n).eval x) μ
  norm_ne : P.squaredNorm μ n square ≠ 0

/-- The local classical domain of the backward recurrence coefficient. -/
structure RecurrenceCInput (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ) where
  square : IntegrableSquare μ (P n)
  next : IntegrableSquare μ (P (n + 1))
  norm_ne : P.squaredNorm μ n square ≠ 0

/-- Positive-definite polynomial integration constructs diagonal coefficient data. -/
abbrev RecurrenceBInput.of (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (hs : Integrable (fun x ↦ (P n).eval x * (P n).eval x) μ := by
      first
      | solve_by_elim (maxDepth := 4) [Polynomial.HasFiniteMoments.integrable_mul, Polynomial.Sequence.IsOrthogonal.integrable]
      | exact (Polynomial.HasPositiveDefiniteIntegral.hasFiniteMoments (by assumption)).integrable_mul _ _
      | aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hx : Integrable (fun x ↦ (X * P n).eval x * (P n).eval x) μ := by
      first
      | solve_by_elim (maxDepth := 4) [Polynomial.HasFiniteMoments.integrable_mul]
      | exact (Polynomial.HasPositiveDefiniteIntegral.hasFiniteMoments (by assumption)).integrable_mul _ _
      | aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hn : P.squaredNorm μ n ⟨hs⟩ ≠ 0 := by
      exact ne_of_gt (Polynomial.Sequence.squaredNorm_pos (by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) _ _)) :
    RecurrenceBInput P μ n := ⟨⟨hs⟩, hx, hn⟩

/-- Construct backward coefficient data from local integrability and nonzero norm. -/
abbrev RecurrenceCInput.of (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (hs : Integrable (fun x ↦ (P n).eval x * (P n).eval x) μ := by
      first
      | solve_by_elim (maxDepth := 4) [Polynomial.HasFiniteMoments.integrable_mul, Polynomial.Sequence.IsOrthogonal.integrable]
      | exact (Polynomial.HasPositiveDefiniteIntegral.hasFiniteMoments (by assumption)).integrable_mul _ _
      | aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (ht : Integrable (fun x ↦ (P (n+1)).eval x * (P (n+1)).eval x) μ := by
      first
      | solve_by_elim (maxDepth := 4) [Polynomial.HasFiniteMoments.integrable_mul, Polynomial.Sequence.IsOrthogonal.integrable]
      | exact (Polynomial.HasPositiveDefiniteIntegral.hasFiniteMoments (by assumption)).integrable_mul _ _
      | aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability]))
    (hn : P.squaredNorm μ n ⟨hs⟩ ≠ 0 := by
      exact ne_of_gt (Polynomial.Sequence.squaredNorm_pos (by aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) _ _)) :
    RecurrenceCInput P μ n := ⟨⟨hs⟩, ⟨ht⟩, hn⟩

/-- The diagonal coefficient in multiplication by X (DLMF 18.2(iv)). -/
noncomputable def recurrenceB (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (d : RecurrenceBInput P μ n) : ℝ :=
  integralInner μ (IntegrablePair.of μ (X * P n) (P n) d.mixed) / P.squaredNorm μ n d.square

/-- The backward coefficient in X Pₙ₊₁ (DLMF 18.2(iv)). -/
noncomputable def recurrenceC (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (d : RecurrenceCInput P μ n) : ℝ :=
  P.recurrenceA n * P.squaredNorm μ (n + 1) d.next / P.squaredNorm μ n d.square

/-- Diagonal coefficient formula on its local classical domain. -/
theorem recurrenceB_apply (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (d : RecurrenceBInput P μ n) :
    P.recurrenceB μ n d =
      integralInner μ (IntegrablePair.of μ (X * P n) (P n) d.mixed) / P.squaredNorm μ n d.square := rfl

/-- Backward coefficient formula on its local classical domain. -/
theorem recurrenceC_apply (P : Sequence ℝ) (μ : Measure ℝ) (n : ℕ)
    (d : RecurrenceCInput P μ n) :
    P.recurrenceC μ n d =
      P.recurrenceA n * P.squaredNorm μ (n + 1) d.next / P.squaredNorm μ n d.square := rfl

/-- Forward coefficients never vanish (DLMF 18.2(iv)). -/
theorem recurrenceA_ne_zero (P : Sequence ℝ) (n : ℕ) : P.recurrenceA n ≠ 0 :=
  div_ne_zero (leadingCoeff_ne_zero.mpr (P.ne_zero n))
    (leadingCoeff_ne_zero.mpr (P.ne_zero (n + 1)))

/-- Backward coefficients never vanish under nondegeneracy (DLMF 18.2(iv)). -/
theorem recurrenceC_ne_zero {μ : Measure ℝ} (hpos : HasPositiveDefiniteIntegral μ)
    (P : Sequence ℝ) (n : ℕ) : P.recurrenceC μ n (Sequence.RecurrenceCInput.of _ _ _) ≠ 0 :=
  div_ne_zero (mul_ne_zero (P.recurrenceA_ne_zero n)
    (ne_of_gt (squaredNorm_pos hpos P (n + 1)))) (ne_of_gt (squaredNorm_pos hpos P n))

/-- The two opposite off-diagonal coefficients have positive product (DLMF 18.2(iv)). -/
theorem recurrenceA_mul_recurrenceC_pos {μ : Measure ℝ}
    (hpos : HasPositiveDefiniteIntegral μ) (P : Sequence ℝ) (n : ℕ) :
    0 < P.recurrenceA n * P.recurrenceC μ n (Sequence.RecurrenceCInput.of _ _ _) := by
  have h : P.recurrenceA n * P.recurrenceC μ n (Sequence.RecurrenceCInput.of _ _ _) =
      P.recurrenceA n ^ 2 * P.squaredNorm μ (n + 1) (IntegrableSquare.of _ _) / P.squaredNorm μ n (IntegrableSquare.of _ _) := by
    unfold recurrenceC; ring
  rw [h]
  exact div_pos (mul_pos (sq_pos_of_ne_zero (P.recurrenceA_ne_zero n))
    (squaredNorm_pos hpos P (n + 1))) (squaredNorm_pos hpos P n)

/-- Forward coefficients equal one in monic normalisation (DLMF 18.2.11_5). -/
theorem recurrenceA_eq_one_of_monic {P : Sequence ℝ} (hmonic : ∀ n, (P n).Monic)
    (n : ℕ) : P.recurrenceA n = 1 := by
  simp [recurrenceA, (hmonic n).leadingCoeff, (hmonic (n + 1)).leadingCoeff]

/-- Backward coefficients are positive in monic normalisation (DLMF 18.2.11_6). -/
theorem recurrenceC_pos_of_monic {μ : Measure ℝ} (hpos : HasPositiveDefiniteIntegral μ)
    {P : Sequence ℝ} (hmonic : ∀ n, (P n).Monic) (n : ℕ) : 0 < P.recurrenceC μ n (Sequence.RecurrenceCInput.of _ _ _) := by
  simpa [recurrenceA_eq_one_of_monic hmonic n] using recurrenceA_mul_recurrenceC_pos hpos P n

/-- Removing the forward term lowers the degree (DLMF 18.2(iv)). -/
theorem degree_X_mul_sub_recurrenceA (P : Sequence ℝ) (n : ℕ) :
    (X * P n - P.recurrenceA n • P (n + 1)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
  have hdeg : (X * P n).degree = ((n + 1 : ℕ) : WithBot ℕ) := by simp [degree_mul, add_comm]
  rw [← hdeg]
  apply degree_sub_lt_left
  · rw [degree_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero (P.recurrenceA_ne_zero n))]
    simp [degree_mul, add_comm]
  · exact mul_ne_zero X_ne_zero (P.ne_zero n)
  · rw [leadingCoeff_smul_of_smul_regular _
      (IsSMulRegular.of_ne_zero (P.recurrenceA_ne_zero n))]
    simp [leadingCoeff_mul, recurrenceA, leadingCoeff_ne_zero.mpr (P.ne_zero (n + 1))]

/-- The integral projection onto the next degree determines the forward coefficient
(DLMF 18.2(iv)). -/
theorem IsOrthogonal.integralInner_X_mul_succ {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ) :
    integralInner μ (IntegrablePair.of μ (X * P n) (P (n + 1))) = P.recurrenceA n * P.squaredNorm μ (n + 1) (IntegrableSquare.of _ _) := by
  have h := hP.integralInner_eq_zero_of_degree_lt hμ (P.degree_X_mul_sub_recurrenceA n)
  rw [integralInner_sub_left hμ, integralInner_smul_left (h := hμ.integrable_mul _ _)] at h
  exact sub_eq_zero.mp h

/-- The reverse projection follows from symmetry of multiplication (DLMF 18.2(iv)). -/
theorem IsOrthogonal.integralInner_X_mul_pred {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ) :
    integralInner μ (IntegrablePair.of μ (X * P (n + 1)) (P n)) = P.recurrenceA n * P.squaredNorm μ (n + 1) (IntegrableSquare.of _ _) := by
  rw [integralInner_X_mul, integralInner_comm]
  exact hP.integralInner_X_mul_succ hμ n

/-- Explicit coefficients in the positive-index three-term recurrence (DLMF 18.2(iv)). -/
theorem IsOrthogonal.three_term {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ) (n : ℕ) :
    X * P (n + 1) = P.recurrenceA (n + 1) • P (n + 2) +
      P.recurrenceB μ (n + 1) (Sequence.RecurrenceBInput.of _ _ _) • P (n + 1) + P.recurrenceC μ n (Sequence.RecurrenceCInput.of _ _ _) • P n := by
  classical
  let hu (i : ℕ) : IsUnit (P i).leadingCoeff :=
    P.isUnit_leadingCoeff i
  let B := P.basis hu
  obtain ⟨a, b, c, heq⟩ := hP.exists_three_term hμ hpos n
  have ha := congrArg (fun p => B.repr p (n + 2)) heq
  have hb := congrArg (fun p => B.repr p (n + 1)) heq
  have hc := congrArg (fun p => B.repr p n) heq
  have hB (i : ℕ) : B.repr (P i) = Finsupp.single i 1 := by
    rw [← P.basis_eq_self hu i]; exact B.repr_self i
  simp only [map_add, map_smul, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul,
    Pi.smul_apply, hB, Finsupp.single_apply, smul_eq_mul] at ha hb hc
  simp at ha hb hc
  rw [hP.basis_repr_eq_integralInner_div hμ hpos hu,
    hP.integralInner_X_mul_succ hμ] at ha
  rw [hP.basis_repr_eq_integralInner_div hμ hpos hu] at hb
  rw [hP.basis_repr_eq_integralInner_div hμ hpos hu,
    hP.integralInner_X_mul_pred hμ] at hc
  have hnorm : P.squaredNorm μ (n + 2) (IntegrableSquare.of _ _) ≠ 0 := ne_of_gt (squaredNorm_pos hpos P (n + 2))
  have ha' : a = P.recurrenceA (n + 1) := by
    change P.recurrenceA (n + 1) * P.squaredNorm μ (n + 2) (IntegrableSquare.of _ _) / P.squaredNorm μ (n + 2) (IntegrableSquare.of _ _) = a at ha
    rw [mul_div_cancel_right₀ _ hnorm] at ha
    exact ha.symm
  have hb' : b = P.recurrenceB μ (n + 1) (Sequence.RecurrenceBInput.of _ _ _) := hb.symm
  have hc' : c = P.recurrenceC μ n (Sequence.RecurrenceCInput.of _ _ _) := hc.symm
  simpa [ha', hb', hc'] using heq

/-- Explicit coefficients in the initial two-term recurrence (DLMF 18.2(iv)). -/
theorem IsOrthogonal.two_term_zero {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) {P : Sequence ℝ} (hP : P.IsOrthogonal μ) :
    X * P 0 = P.recurrenceA 0 • P 1 + P.recurrenceB μ 0 (Sequence.RecurrenceBInput.of _ _ _) • P 0 := by
  classical
  let hu (i : ℕ) : IsUnit (P i).leadingCoeff :=
    P.isUnit_leadingCoeff i
  let B := P.basis hu
  obtain ⟨a, b, heq⟩ := hP.exists_two_term_zero hμ hpos
  have ha := congrArg (fun p => B.repr p 1) heq
  have hb := congrArg (fun p => B.repr p 0) heq
  have hB (i : ℕ) : B.repr (P i) = Finsupp.single i 1 := by
    rw [← P.basis_eq_self hu i]; exact B.repr_self i
  simp only [map_add, map_smul, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul,
    Pi.smul_apply, hB, Finsupp.single_apply, smul_eq_mul] at ha hb
  norm_num at ha hb
  rw [hP.basis_repr_eq_integralInner_div hμ hpos hu,
    hP.integralInner_X_mul_succ hμ] at ha
  rw [hP.basis_repr_eq_integralInner_div hμ hpos hu] at hb
  have ha' : a = P.recurrenceA 0 := by
    change P.recurrenceA 0 * P.squaredNorm μ 1 (IntegrableSquare.of _ _) / P.squaredNorm μ 1 (IntegrableSquare.of _ _) = a at ha
    rw [mul_div_cancel_right₀ _ (ne_of_gt (squaredNorm_pos hpos P 1))] at ha
    exact ha.symm
  have hb' : b = P.recurrenceB μ 0 (Sequence.RecurrenceBInput.of _ _ _) := hb.symm
  simpa [ha', hb'] using heq

end Polynomial.Sequence
