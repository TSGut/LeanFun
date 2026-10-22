/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.MeasureModification
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Recurrence
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Parity

/-!
# Support of polynomial measure-conversion coefficients

A polynomial modification of degree d gives an upper connection of bandwidth d.
For even measures, opposite parity coefficients vanish as well. These statements
are independent of classical-family formulas or connectedness of support.
Reference: Gautschi, *Orthogonal Polynomials*; Gutleb–Olver–Slevinsky,
polynomial measure modification and triangular connection factors.
-/

public section
open MeasureTheory
namespace Polynomial

/-- Opposite reflection parities are orthogonal for an even measure. -/
theorem integralInner_eq_zero_of_opposite_parity {μ : Measure ℝ} [μ.IsNegInvariant]
    {p q : ℝ[X]} {n m : ℕ}
    (hp : p.comp (-X) = C ((-1 : ℝ) ^ n) * p)
    (hq : q.comp (-X) = C ((-1 : ℝ) ^ m) * q) (hnm : n % 2 ≠ m % 2)
    (hi : Integrable (fun x => p.eval x * q.eval x) μ := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) :
    integralInner μ (IntegrablePair.of μ p q) = 0 := by
  have hep (x : ℝ) : p.eval (-x) = (-1 : ℝ) ^ n * p.eval x := by
    simpa using congrArg (fun r : ℝ[X] => r.eval x) hp
  have heq (x : ℝ) : q.eval (-x) = (-1 : ℝ) ^ m * q.eval x := by
    simpa using congrArg (fun r : ℝ[X] => r.eval x) hq
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ m = -1 := by
    rw [neg_one_pow_eq_pow_mod_two n, neg_one_pow_eq_pow_mod_two m]
    have h : (n % 2 = 0 ∧ m % 2 = 1) ∨ (n % 2 = 1 ∧ m % 2 = 0) := by omega
    rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp [h₁,h₂]
  have he := integral_neg_eq_self (fun x => p.eval x * q.eval x) μ
  simp_rw [hep, heq, show ∀ x, (-1 : ℝ) ^ n * p.eval x *
    ((-1 : ℝ) ^ m * q.eval x) =
    ((-1 : ℝ) ^ n * (-1 : ℝ) ^ m) * (p.eval x * q.eval x) by intro x; ring] at he
  rw [hs, integral_const_mul] at he
  change (-1 : ℝ) * integralInner μ (IntegrablePair.of μ p q) = integralInner μ (IntegrablePair.of μ p q) at he
  linarith

namespace Sequence

/-- Connection coefficients vanish above the degree of the expanded polynomial. -/
theorem IsOrthogonal.basis_repr_eq_zero_of_natDegree_lt {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    {Q : Sequence ℝ} (hQ : Q.IsOrthogonal μ) (hu : ∀ i, IsUnit (Q i).leadingCoeff)
    {p : ℝ[X]} {m : ℕ} (hm : p.natDegree < m) : (Q.basis hu).repr p m = 0 := by
  rw [hQ.basis_repr_eq_integralInner_div hμ hpos hu,
    hQ.integralInner_eq_zero_of_degree_lt hμ
      (degree_le_natDegree.trans_lt (by exact_mod_cast hm)), zero_div]

/-- The mixed pairing vanishes beyond the degree bandwidth of a measure modification. -/
theorem IsOrthogonal.integralInner_eq_zero_of_polynomial_modification
    {μ : Measure ℝ} (hμ : HasFiniteMoments μ) (u : ℝ[X])
    (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x) {P Q : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (hQ : Q.IsOrthogonal (Polynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)))
    {n m : ℕ} (hout : n < m ∨ m + u.natDegree < n) :
    integralInner (Polynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) (IntegrablePair.of (Polynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)) (P n) (Q m)) = 0 := by
  rcases hout with hout | hout
  · exact hQ.integralInner_eq_zero_of_degree_lt (hμ.polynomialDensityMeasure u hu)
      (by simpa only [P.degree_eq, Nat.cast_lt] using hout)
  · rw [integralInner_comm, integralInner_polynomialDensityMeasure_comap u (Q m) (P n) hu (hpq := hμ.integrable_mul _ _)]
    have hd : (u * Q m).natDegree < n := natDegree_mul_le.trans_lt (by
      simpa only [Q.natDegree_eq, Nat.add_comm] using hout)
    exact hP.integralInner_eq_zero_of_degree_lt hμ
      (degree_le_natDegree.trans_lt (by exact_mod_cast hd))

/-- Equal-degree pairing with a positively oriented orthogonal polynomial is positive. -/
theorem IsOrthogonal.integralInner_pos_of_leadingCoeff_pos {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) {Q : Sequence ℝ} (hQ : Q.IsOrthogonal μ)
    {p : ℝ[X]} {n : ℕ} (hp : p.natDegree = n) (hpl : 0 < p.leadingCoeff)
    (hQl : 0 < (Q n).leadingCoeff) (hQn : 0 < integralInner μ (IntegrablePair.of μ (Q n) (Q n))) :
    0 < integralInner μ (IntegrablePair.of μ p (Q n)) := by
  let c := p.leadingCoeff / (Q n).leadingCoeff
  have hc : 0 < c := div_pos hpl hQl
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp hpl.ne'
  have hd : (p-c • Q n).degree < n := by
    have ht := degree_sub_lt_left
      (show p.degree = (c • Q n).degree by
        rw [degree_eq_natDegree hp0, hp,
          degree_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc.ne'), Q.degree_eq])
      hp0 (show p.leadingCoeff = (c • Q n).leadingCoeff by
        rw [leadingCoeff_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc.ne')]
        simp [c, hQl.ne'])
    simpa only [degree_eq_natDegree hp0, hp] using ht
  have he := hQ.integralInner_eq_zero_of_degree_lt hμ hd
  rw [integralInner_sub_left hμ, integralInner_smul_left (h := hμ.integrable_mul _ _)] at he
  have h : integralInner μ (IntegrablePair.of μ p (Q n)) = c * integralInner μ (IntegrablePair.of μ (Q n) (Q n)) := by linarith
  rw [h]
  exact mul_pos hc hQn

/-- A degree-d polynomial modification gives connection bandwidth d. -/
theorem IsOrthogonal.basis_repr_eq_zero_of_polynomial_modification {u : ℝ[X]} {μ : Measure {x : ℝ // 0 ≤ u.eval x}}
    (hμ : HasFiniteMoments (μ.map Subtype.val))
    (hpos : HasPositiveDefiniteIntegral (μ.map Subtype.val)) (hu0 : u ≠ 0)
    {P Q : Sequence ℝ} (hP : P.IsOrthogonal (μ.map Subtype.val))
    (hQ : Q.IsOrthogonal (polynomialDensityMeasure u μ))
    (hunits : ∀ i, IsUnit (Q i).leadingCoeff) {n m : ℕ}
    (hout : n < m ∨ m + u.natDegree < n) : (Q.basis hunits).repr (P n) m = 0 := by
  have hν := HasFiniteMoments.withDensity_polynomial hμ
  have hνpos := HasPositiveDefiniteIntegral.withDensity_polynomial hμ hpos hu0
  rcases hout with hout | hout
  · exact hQ.basis_repr_eq_zero_of_natDegree_lt hν hνpos hunits (by simpa using hout)
  rw [hQ.basis_repr_eq_integralInner_div hν hνpos hunits,
    integralInner_comm _ (P n), integralInner_polynomialDensityMeasure (Q m) (P n) (hμ.integrable_mul _ _)]
  have hd : (u * Q m).natDegree < n := (natDegree_mul_le.trans_lt (by
    simpa only [Q.natDegree_eq, Nat.add_comm] using hout))
  rw [hP.integralInner_eq_zero_of_degree_lt hμ
    (degree_le_natDegree.trans_lt (by exact_mod_cast hd)), zero_div]


/-- Transport from a real source supported on the nonnegative locus. -/
theorem IsOrthogonal.basis_repr_eq_zero_of_polynomial_modification_comap
    {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) (u : ℝ[X]) (hu0 : u ≠ 0)
    (hu : ∀ᵐ x ∂μ, 0 ≤ u.eval x) {P Q : Sequence ℝ} (hP : P.IsOrthogonal μ)
    (hQ : Q.IsOrthogonal (Polynomial.polynomialDensityMeasure (u) ((μ).comap Subtype.val)))
    (hunits : ∀ i, IsUnit (Q i).leadingCoeff) {n m : ℕ}
    (hout : n < m ∨ m + u.natDegree < n) : (Q.basis hunits).repr (P n) m = 0  := by
  have hm : HasFiniteMoments ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  have hp : HasPositiveDefiniteIntegral ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  have hP' : P.IsOrthogonal ((μ.comap (Subtype.val : {x : ℝ // 0 ≤ u.eval x} → ℝ)).map Subtype.val) := by
    rwa [map_comap_polynomial_nonneg u μ hu]
  exact IsOrthogonal.basis_repr_eq_zero_of_polynomial_modification hm hp hu0 hP' hQ hunits hout

/-- Reflection parity removes every other diagonal of an even-measure connection. -/
theorem IsOrthogonal.basis_repr_eq_zero_of_parity
    {μ ν : Measure ℝ} [μ.IsNegInvariant] [ν.IsNegInvariant]
    (hμ : HasFiniteMoments μ) (hpos : HasPositiveDefiniteIntegral μ)
    (hν : HasFiniteMoments ν) (hνpos : HasPositiveDefiniteIntegral ν)
    {P Q : Sequence ℝ} (hP : P.IsOrthogonal μ) (hQ : Q.IsOrthogonal ν)
    (hu : ∀ i, IsUnit (Q i).leadingCoeff) {n m : ℕ} (hnm : n % 2 ≠ m % 2) :
    (Q.basis hu).repr (P n) m = 0 := by
  rw [hQ.basis_repr_eq_integralInner_div hν hνpos hu,
    integralInner_eq_zero_of_opposite_parity (hP.comp_neg_X hμ hpos n)
      (hQ.comp_neg_X hν hνpos m) hnm, zero_div]

end Sequence
end Polynomial
