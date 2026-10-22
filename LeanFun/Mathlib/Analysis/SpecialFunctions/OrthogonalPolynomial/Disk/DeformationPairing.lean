/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Deformation
public import LeanFun.Mathlib.RingTheory.Polynomial.EvenTransport
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Uniqueness

/-!
# Orthonormal outer polynomials under disk deformation

The even transport is an isometry after the exact degree-shift normalization.
Uniqueness then identifies it with the chosen orthonormal outer sequence.
Reference: Dunkl–Xu, §2.6.1; Szegő, Chapter 3 (uniqueness).
-/

public section
open MeasureTheory Set
namespace Polynomial

/-- Transport scales the shifted polynomial pairing by `δ^k`. -/
theorem integralInner_evenDiskTransport {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ) (p q : ℝ[X])
    (hp : ∀ i, i % 2 ≠ 0 → p.coeff i = 0)
    (hq : ∀ i, i % 2 ≠ 0 → q.coeff i = 0) :
    integralInner (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (evenDiskTransport ⟨δ,hδ.ne'⟩ p) (evenDiskTransport ⟨δ,hδ.ne'⟩ q) (h := ((hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) _).integrable_mul _ _)) =
      δ^k * integralInner (diskOuterMeasure k (μ.comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure k (μ.comap Subtype.val)) p q (h := ((hasFiniteMoments_of_ae_mem_Icc hx).diskOuterMeasure hx _).integrable_mul _ _)) := by
  unfold integralInner
  rw [integral_diskOuterMeasure_diskDeformedMeasure_even hx hδ.le hδ1 k
    (by fun_prop) (by
      intro x
      dsimp only
      exact congrArg₂ (fun a b : ℝ => a*b)
        (even_eval_evenDiskTransport ⟨δ,hδ.ne'⟩ p x) (even_eval_evenDiskTransport ⟨δ,hδ.ne'⟩ q x))]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [eval_evenDiskTransport_sq δ hδ.ne' p hp _ t (diskDeformation_sq_of_unitInterval hδ.le hδ1 t),
    eval_evenDiskTransport_sq δ hδ.ne' q hq _ t (diskDeformation_sq_of_unitInterval hδ.le hδ1 t)]

/-- The factor `δ⁻¹^b` makes transport an isometry at inner degree `2*b`. -/
theorem integralInner_normalized_evenDiskTransport {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (b : ℕ) (p q : ℝ[X])
    (hp : ∀ i, i % 2 ≠ 0 → p.coeff i = 0)
    (hq : ∀ i, i % 2 ≠ 0 → q.coeff i = 0) :
    integralInner (diskOuterMeasure (2*b) ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure (2*b) ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (δ⁻¹^b • evenDiskTransport ⟨δ,hδ.ne'⟩ p) (δ⁻¹^b • evenDiskTransport ⟨δ,hδ.ne'⟩ q) (h := ((hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) _).integrable_mul _ _)) =
      integralInner (diskOuterMeasure (2*b) (μ.comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure (2*b) (μ.comap Subtype.val)) p q (h := ((hasFiniteMoments_of_ae_mem_Icc hx).diskOuterMeasure hx _).integrable_mul _ _)) := by
  have hμδ := (hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure
    (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) (2*b)
  rw [integralInner_smul_left (h := hμδ.integrable_mul _ _), integralInner_comm _ (evenDiskTransport ⟨δ,hδ.ne'⟩ p),
    integralInner_smul_left (h := hμδ.integrable_mul _ _), integralInner_comm _ (evenDiskTransport ⟨δ,hδ.ne'⟩ q),
    integralInner_evenDiskTransport hx hδ hδ1 (2*b) p q hp hq]
  have he : δ⁻¹^b * (δ⁻¹^b * δ^(2*b)) = 1 := by
    rw [pow_mul]
    calc
      _ = (δ⁻¹ * δ)^(2*b) := by rw [mul_pow, pow_mul]; ring
      _ = 1 := by rw [inv_mul_cancel₀ hδ.ne', one_pow]
  calc
    _ = (δ⁻¹^b * (δ⁻¹^b * δ^(2*b))) * integralInner (diskOuterMeasure (2*b) (μ.comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure (2*b) (μ.comap Subtype.val)) p q (h := ((hasFiniteMoments_of_ae_mem_Icc hx).diskOuterMeasure hx _).integrable_mul _ _)) := by ring
    _ = _ := by rw [he, one_mul]
/-- Even orthogonal polynomials agree up to their leading-coefficient ratio after transport. -/
theorem evenDiskTransport_eq_leadingCoeff_div_smul
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hμ : HasFiniteMoments μ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k n : ℕ)
    (hpos : HasPositiveDefiniteIntegral (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)))
    {P Q : Sequence ℝ} (hP : P.IsOrthogonal (diskOuterMeasure k (μ.comap Subtype.val)))
    (hQ : Q.IsOrthogonal (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)))
    (hp : ∀ i, i % 2 ≠ 0 → (P n).coeff i = 0)
    (hq : ∀ i, i % 2 ≠ 0 → (Q n).coeff i = 0)
    (hl : 0 < (P n).leadingCoeff) :
    evenDiskTransport ⟨δ,hδ.ne'⟩ (P n) =
      ((evenDiskTransport ⟨δ,hδ.ne'⟩ (P n)).leadingCoeff / (Q n).leadingCoeff) • Q n := by
  let t := evenDiskTransport ⟨δ,hδ.ne'⟩ (P n)
  let c := t.leadingCoeff / (Q n).leadingCoeff
  let d := t-c • Q n
  have ht : 0 < t.leadingCoeff := leadingCoeff_evenDiskTransport_pos δ hδ (P n) hp hl
  have ht0 : t ≠ 0 := leadingCoeff_ne_zero.mp ht.ne'
  have hq0 := leadingCoeff_ne_zero.mpr (Q.ne_zero n)
  have hc : c ≠ 0 := div_ne_zero ht.ne' hq0
  have htn : t.natDegree = n := by
    change (evenDiskTransport ⟨δ,hδ.ne'⟩ (P n)).natDegree = n
    rw [natDegree_evenDiskTransport δ hδ.ne' (P n) hp, P.natDegree_eq]
  have htd : t.degree = n := by rw [degree_eq_natDegree ht0, htn]
  have hdd : d.degree < n := by
    have he : t.degree = (c • Q n).degree := by
      rw [degree_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc), Q.degree_eq, htd]
    have hh : t.leadingCoeff = (c • Q n).leadingCoeff := by
      rw [leadingCoeff_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc)]
      dsimp [c]
      field_simp
    exact htd ▸ degree_sub_lt_left he ht0 hh
  have hdpar : ∀ i, i % 2 ≠ 0 → d.coeff i = 0 := by
    intro i hi
    simp only [d, coeff_sub, coeff_smul, t, coeff_evenDiskTransport_eq_zero ⟨δ,hδ.ne'⟩ (P n) i hi,
      hq i hi, smul_zero, sub_zero]
  let e := evenDiskTransport ⟨δ⁻¹,inv_ne_zero hδ.ne'⟩ d
  have hepar : ∀ i, i % 2 ≠ 0 → e.coeff i = 0 := coeff_evenDiskTransport_eq_zero _ d
  have hed : e.degree < n := by
    by_cases hd0 : d = 0
    · simp [e, hd0, evenDiskTransport, contract]
    · have hen : e.natDegree = d.natDegree := natDegree_evenDiskTransport _ (inv_ne_zero hδ.ne') d hdpar
      rw [degree_eq_natDegree hd0] at hdd
      exact lt_of_le_of_lt (degree_le_of_natDegree_le (by rw [hen])) hdd
  have hte : evenDiskTransport ⟨δ,hδ.ne'⟩ e = d := by
    have hh := evenDiskTransport_inv δ⁻¹ (inv_ne_zero hδ.ne') d hdpar
    simpa only [inv_inv] using hh
  have hz := hP.integralInner_eq_zero_of_degree_lt (hμ.diskOuterMeasure hx k) hed
  have hμδ := (hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure
    (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) k
  have hdt : integralInner (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) d t (h := ((hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) _).integrable_mul _ _)) = 0 := by
    change integralInner (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) d (evenDiskTransport ⟨δ,hδ.ne'⟩ (P n)) (h := ((hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) _).integrable_mul _ _)) = 0
    have heq := congrArg (fun q => integralInner _ (hμδ.pair q (P n |> evenDiskTransport ⟨δ,hδ.ne'⟩))) hte
    rw [← heq, integralInner_evenDiskTransport hx hδ hδ1 k e (P n) hepar hp, hz, mul_zero]
  have hdq := hQ.integralInner_eq_zero_of_degree_lt hμδ hdd
  have hself : integralInner (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) d d (h := ((hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) _).integrable_mul _ _)) = 0 := by
    change integralInner (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure k ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) d (t-c • Q n) (h := ((hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) _).integrable_mul _ _)) = 0
    rw [integralInner_comm, integralInner_sub_left hμδ, integralInner_smul_left (h := hμδ.integrable_mul _ _),
      integralInner_comm _ t, integralInner_comm _ (Q n), hdt, hdq]
    ring
  exact sub_eq_zero.mp (hpos.eq_zero_of_integralInner_self_eq_zero hself)
/-- Positive-leading unit normalization makes the even transport equal the target polynomial. -/
theorem normalized_evenDiskTransport_eq
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hμ : HasFiniteMoments μ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (b n : ℕ)
    (hpos : HasPositiveDefiniteIntegral (diskOuterMeasure (2*b) ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)))
    {P Q : Sequence ℝ} (hP : P.IsOrthogonal (diskOuterMeasure (2*b) (μ.comap Subtype.val)))
    (hQ : Q.IsOrthogonal (diskOuterMeasure (2*b) ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)))
    (hp : ∀ i, i % 2 ≠ 0 → (P n).coeff i = 0)
    (hq : ∀ i, i % 2 ≠ 0 → (Q n).coeff i = 0)
    (hpl : 0 < (P n).leadingCoeff) (hql : 0 < (Q n).leadingCoeff)
    (hpn : integralInner (diskOuterMeasure (2*b) (μ.comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure (2*b) (μ.comap Subtype.val)) (P n) (P n) (h := ((hasFiniteMoments_of_ae_mem_Icc hx).diskOuterMeasure hx _).integrable_mul _ _)) = 1)
    (hqn : integralInner (diskOuterMeasure (2*b) ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (IntegrablePair.of (diskOuterMeasure (2*b) ((diskDeformedMeasure δ (μ.comap Subtype.val)).comap Subtype.val)) (Q n) (Q n) (h := ((hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) _).integrable_mul _ _)) = 1) :
    δ⁻¹^b • evenDiskTransport ⟨δ,hδ.ne'⟩ (P n) = Q n := by
  let c := (evenDiskTransport ⟨δ,hδ.ne'⟩ (P n)).leadingCoeff / (Q n).leadingCoeff
  have hc : 0 < c := div_pos (leadingCoeff_evenDiskTransport_pos δ hδ (P n) hp hpl) hql
  have he : evenDiskTransport ⟨δ,hδ.ne'⟩ (P n) = c • Q n :=
    evenDiskTransport_eq_leadingCoeff_div_smul hx hμ hδ hδ1 (2*b) n hpos hP hQ hp hq hpl
  have hn := integralInner_evenDiskTransport hx hδ hδ1 (2*b) (P n) (P n) hp hp
  have hμδ := (hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 hx).diskOuterMeasure
    (ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 hx) (2*b)
  have heq := congrArg (fun q => integralInner _ (hμδ.pair q q)) he
  rw [heq, integralInner_smul_left (h := hμδ.integrable_mul _ _), integralInner_comm _ (Q n),
    integralInner_smul_left (h := hμδ.integrable_mul _ _), hqn, hpn] at hn
  have hec : c = δ^b := by
    have hpow : δ^(2*b) = (δ^b)^2 := by rw [Nat.mul_comm, pow_mul]
    rw [hpow] at hn
    nlinarith [pow_pos hδ b]
  rw [he, hec, smul_smul, ← mul_pow, inv_mul_cancel₀ hδ.ne', one_pow, one_smul]

end Polynomial
