/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.TerminatingDomain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalWeighted
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerRecurrence
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalDifferentiation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.Polynomial
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gamma.Domain
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
/-! # Classical polynomial power-law outputs
Gamma factors are non-polar. A finite mode requires only the recurrence
 denominators used through that mode; whole-family data certify all steps.
Reference: Gutleb--Carrillo--Olver, arXiv:2011.00045, Lemma2.7 andTheorem2.4.
-/
@[expose] public noncomputable section
open Polynomial Set
namespace Real
/-- The exact non-pole domain of the three Gamma factors in the initial mode. -/
structure PowerLawInitialData where
  alpha : ℝ
  lam : ℝ
  alphaRegular : ∀ n : ℕ, (alpha+1)/2 ≠ -(n : ℝ)
  lamRegular : ∀ n : ℕ, lam+1/2 ≠ -(n : ℝ)
  sumRegular : ∀ n : ℕ, lam+alpha/2+1 ≠ -(n : ℝ)
/-- Shifting the kernel exponent by two shifts the relevant Gamma arguments by one. -/
def PowerLawInitialData.shift (p : PowerLawInitialData) : PowerLawInitialData where
  alpha := p.alpha+2
  lam := p.lam
  alphaRegular n h := by
    apply p.alphaRegular (n+1)
    push_cast
    linarith
  lamRegular := p.lamRegular
  sumRegular n h := by
    apply p.sumRegular (n+1)
    push_cast
    linarith
/-- Every parameter pair in the natural integrable range is admissible. -/
def PowerLawInitialData.ofIntegrable (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ)) : PowerLawInitialData where
  alpha := α.val
  lam := lam.val
  alphaRegular := (GammaPoint.ofPos _ (by linarith [show -1 < α.val from α.property])).property
  lamRegular := (GammaPoint.ofPos _ (by linarith [show -(1/2) < lam.val from lam.property])).property
  sumRegular := (GammaPoint.ofPos _ (by linarith [show -1 < α.val from α.property, show -(1/2) < lam.val from lam.property])).property
/-- Finite-prefix recurrence data require exactly the denominators actually used. -/
structure PowerLawRecurrenceData (n : ℕ) extends PowerLawInitialData where
  firstDenominator : 1 ≤ n → alpha+2 ≠ 0
  leadingDenominator : ∀ m : ℕ, m+2 ≤ n → (m : ℝ)+2*lam+alpha+2 ≠ 0
/-- Restricting admissibility to an earlier mode requires no extra assumption. -/
def PowerLawRecurrenceData.truncate {n : ℕ} (p : PowerLawRecurrenceData n)
    (m : ℕ) (hm : m ≤ n) : PowerLawRecurrenceData m where
  toPowerLawInitialData := p.toPowerLawInitialData
  firstDenominator h := p.firstDenominator (h.trans hm)
  leadingDenominator k hk := p.leadingDenominator k (hk.trans hm)
/-- Natural integrable parameters certify every finite recurrence prefix. -/
def PowerLawRecurrenceData.ofIntegrable (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (n : ℕ) : PowerLawRecurrenceData n where
  toPowerLawInitialData := .ofIntegrable α lam
  firstDenominator _ := by
    change α.val+2 ≠ 0
    linarith [show -1 < α.val from α.property]
  leadingDenominator m _ := by
    change (m : ℝ)+2*lam.val+α.val+2 ≠ 0
    linarith [show -1 < α.val from α.property, show -(1/2) < lam.val from lam.property, Nat.cast_nonneg (α := ℝ) m]

/-- The initial polynomial uses only defined Gamma values and a terminating Gauss polynomial. -/
def powerLawGegenbauerInitialPolynomial (p : PowerLawInitialData) (k : ℕ) : ℝ[X] :=
  C (GammaOn ⟨(p.alpha+1)/2,p.alphaRegular⟩ * GammaOn ⟨p.lam+1/2,p.lamRegular⟩ /
    GammaOn ⟨p.lam+p.alpha/2+1,p.sumRegular⟩) *
    (ordinaryHypergeometricPolynomial k (.ofNoPole (-p.alpha/2) (1/2 : ℝ) k
      (by intro n hn; have h := Nat.cast_nonneg (α := ℝ) n; linarith))).comp (X^2)
/-- Each finite mode is defined only when the denominators it actually uses are nonzero. -/
def powerLawGegenbauerPolynomial (k : ℕ) : (n : ℕ) → PowerLawRecurrenceData n → ℝ[X]
  | 0, p => powerLawGegenbauerInitialPolynomial p.toPowerLawInitialData k
  | 1, p => C (2*p.lam)*(X*powerLawGegenbauerInitialPolynomial p.toPowerLawInitialData k -
      C ((p.alpha+2)⁻¹)*(powerLawGegenbauerInitialPolynomial p.toPowerLawInitialData.shift (k+1)).derivative)
  | m+2, p => C ((((m : ℝ)+1)*((m : ℝ)+2)*((m : ℝ)+2*p.lam+p.alpha+2))⁻¹) *
      (C (2*((m : ℝ)+p.lam+1)*((m : ℝ)+1)*((m : ℝ)+1+2*p.lam))*X*
        powerLawGegenbauerPolynomial k (m+1) (p.truncate (m+1) (by omega)) -
      C (((m : ℝ)+1+2*p.lam)*((m : ℝ)-p.alpha)*((m : ℝ)+2*p.lam))*
        powerLawGegenbauerPolynomial k m (p.truncate m (by omega)))
end Real
namespace Real
/-- The full recurrence denominator is nonzero whenever this step is in the prefix. -/
theorem PowerLawRecurrenceData.denominator_ne_zero {n : ℕ} (p : PowerLawRecurrenceData n)
    (m : ℕ) (hm : m+2 ≤ n) :
    ((m : ℝ)+1)*((m : ℝ)+2)*((m : ℝ)+2*p.lam+p.alpha+2) ≠ 0 := by
  have hn := Nat.cast_nonneg (α := ℝ) m
  exact mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (p.leadingDenominator m hm)
/-- Initial degree does not require positivity or power-law compatibility. -/
theorem natDegree_powerLawGegenbauerInitialPolynomial_le (p : PowerLawInitialData) (k : ℕ) :
    (powerLawGegenbauerInitialPolynomial p k).natDegree ≤ 2*k := by
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_comp, natDegree_X_pow]
  have h := natDegree_ordinaryHypergeometricPolynomial_le k (.ofNoPole (-p.alpha/2) (1/2 : ℝ) k
    (by intro n hn; have h := Nat.cast_nonneg (α := ℝ) n; linarith))
  omega
/-- The finite-prefix degree estimate preserves every nonsingular classical recurrence. -/
theorem natDegree_powerLawGegenbauerPolynomial_le (k n : ℕ) :
    ∀ p : PowerLawRecurrenceData n, (powerLawGegenbauerPolynomial k n p).natDegree ≤ n+2*k := by
  induction n using Nat.twoStepInduction with
  | zero =>
    intro p
    simpa only [powerLawGegenbauerPolynomial, zero_add] using
      natDegree_powerLawGegenbauerInitialPolynomial_le p.toPowerLawInitialData k
  | one =>
    intro p
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · have h := natDegree_powerLawGegenbauerInitialPolynomial_le p.toPowerLawInitialData k
      exact natDegree_mul_le.trans (by simpa only [natDegree_X] using Nat.add_le_add_left h 1)
    · apply (natDegree_C_mul_le _ _).trans
      have h := natDegree_powerLawGegenbauerInitialPolynomial_le p.toPowerLawInitialData.shift (k+1)
      have hd := natDegree_derivative_le (powerLawGegenbauerInitialPolynomial p.toPowerLawInitialData.shift (k+1))
      omega
  | more m hm hm1 =>
    intro p
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · rw [mul_assoc]
      apply (natDegree_C_mul_le _ _).trans
      have hd := natDegree_mul_le (p := (X : ℝ[X]))
        (q := powerLawGegenbauerPolynomial k (m+1) (p.truncate (m+1) (by omega)))
      rw [natDegree_X] at hd
      have h := hm1 (p.truncate (m+1) (by omega))
      omega
    · exact (natDegree_C_mul_le _ _).trans ((hm (p.truncate m (by omega))).trans (by omega))
end Real
namespace Real
/-- A polynomial operator on all degrees needs all recurrence steps to be classical. -/
structure PowerLawFamilyData extends PowerLawInitialData where
  firstDenominator : alpha+2 ≠ 0
  leadingDenominator : ∀ m : ℕ, (m : ℝ)+2*lam+alpha+2 ≠ 0
/-- Every finite mode inherits the family's nonsingular data. -/
def PowerLawFamilyData.atDegree (p : PowerLawFamilyData) (n : ℕ) : PowerLawRecurrenceData n where
  toPowerLawInitialData := p.toPowerLawInitialData
  firstDenominator _ := p.firstDenominator
  leadingDenominator m _ := p.leadingDenominator m
/-- The natural integrable range provides a whole classical polynomial family. -/
def PowerLawFamilyData.ofIntegrable (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ)) : PowerLawFamilyData where
  toPowerLawInitialData := .ofIntegrable α lam
  firstDenominator := by
    change α.val+2 ≠ 0
    linarith [show -1 < α.val from α.property]
  leadingDenominator m := by
    change (m : ℝ)+2*lam.val+α.val+2 ≠ 0
    linarith [show -1 < α.val from α.property,show -(1/2) < lam.val from lam.property,Nat.cast_nonneg (α := ℝ) m]
end Real

namespace Real

end Real
namespace Real

end Real

namespace Real
private theorem gauss_value_congr {K : Type*} [RCLike K] {p q : GaussParameters K}
    (ha : p.a = q.a) (hb : p.b = q.b) (hc : p.c = q.c)
    (z : GaussSeriesPoint p) (w : GaussSeriesPoint q) (hz : z.val = w.val) :
    ordinaryHypergeometricOn p z = ordinaryHypergeometricOn q w := by
  have hp : p = q := by
    cases p; cases q
    simp_all
  subst q
  congr 1
  exact Subtype.ext hz


set_option maxHeartbeats 400000 in
/-- Classical integral evaluation of the initial terminating polynomial. -/
theorem eval_powerLawGegenbauerInitialPolynomial (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) {k : ℕ} (hk : lam.val+α.val/2 = k)
    (x : Ioo (-1 : ℝ) 1) :
    (powerLawGegenbauerInitialPolynomial (.ofIntegrable α lam) k).eval x.val =
      powerLawIntegral (.gegenbauerWeight α lam x) := by
  rw [powerLawIntegral_gegenbauerWeight_hypergeometricSqOn]
  let p : TerminatingGaussParameters ℝ k :=
    .ofNoPole (-α.val/2) (1/2 : ℝ) k
      (by intro n hn; have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have he := ordinaryHypergeometric_eq_eval_polynomial k p (x.val^2)
  let q : GaussParameters ℝ := GaussParameters.ofNoPole (-α.val/2) (-lam.val-α.val/2) (1/2 : ℝ)
    (GammaPoint.ofPos _ (by norm_num)).property
  let z : Metric.ball (0 : ℝ) 1 := ⟨x.val^2, by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [x.property.1,x.property.2]⟩
  have hc : ordinaryHypergeometricOn q (.ofUnitDisk q z) =
      ordinaryHypergeometricOn p.val (.ofTerminating p.val k (Or.inr p.property) (x.val^2)) := by
    apply gauss_value_congr
    · rfl
    · change -lam.val-α.val/2 = -(k : ℝ)
      linarith
    · rfl
    · rfl
  rw [hc, he]
  simp only [powerLawGegenbauerInitialPolynomial, PowerLawInitialData.ofIntegrable,
    GammaOn, GammaPoint.ofPos, eval_mul, eval_C, eval_comp, eval_pow, eval_X, p]

/-- Classical integral evaluation of each finite recurrence mode. -/
theorem eval_powerLawGegenbauerPolynomial (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) {k : ℕ} (hk : lam.val+α.val/2 = k)
    (x : Ioo (-1 : ℝ) 1) (n : ℕ) :
    (powerLawGegenbauerPolynomial k n (.ofIntegrable α lam n)).eval x.val =
      powerLawIntegral (.gegenbauerMode α lam x n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simpa only [powerLawGegenbauerPolynomial, PowerLawRecurrenceData.ofIntegrable,
      PowerLawInput.gegenbauerMode_zero] using
      eval_powerLawGegenbauerInitialPolynomial α lam hk x
  | one =>
    let α' : Ioi (-1 : ℝ) := ⟨α.val+2, by change -1 < α.val+2; linarith [show -1 < α.val from α.property]⟩
    let P := powerLawGegenbauerInitialPolynomial
      (PowerLawInitialData.ofIntegrable α lam).shift (k+1)
    have hk' : lam.val+α'.val/2 = (k+1 : ℕ) := by dsimp [α']; push_cast; linarith
    obtain ⟨d,hd,hm⟩ := powerLawIntegral_gegenbauer_one_hasDerivOn α lam x
    have he (t : Ioo (-1 : ℝ) 1) : P.eval t.val =
        powerLawIntegral (.gegenbauerWeight α' lam t) :=
      eval_powerLawGegenbauerInitialPolynomial α' lam hk' t
    have hp : HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1,isOpen_Ioo⟩
        (fun t ↦ powerLawIntegral (.gegenbauerWeight α' lam t)) (P.derivative.eval x.val) x :=
      ⟨fun t ↦ P.eval t,he,P.hasDerivAt x.val⟩
    have hd' : d = P.derivative.eval x.val := hd.unique hp
    rw [hm,hd']
    simp only [powerLawGegenbauerPolynomial, PowerLawRecurrenceData.ofIntegrable,
      eval_mul, eval_sub, eval_C, eval_X]
    rw [eval_powerLawGegenbauerInitialPolynomial α lam hk x]
    dsimp only [PowerLawInitialData.ofIntegrable, P]
    ring
  | more m hm hm1 =>
    have hr := powerLawIntegral_gegenbauer_recurrenceOn α lam x m
    dsimp only at hr
    have hb : ((m : ℝ)+1)*((m : ℝ)+2)*((m : ℝ)+2*lam.val+α.val+2) ≠ 0 :=
      (PowerLawRecurrenceData.ofIntegrable α lam (m+2)).denominator_ne_zero m le_rfl
    simp only [powerLawGegenbauerPolynomial, PowerLawRecurrenceData.ofIntegrable,
      PowerLawRecurrenceData.truncate, PowerLawInitialData.ofIntegrable,
      eval_mul, eval_sub, eval_C, eval_X] at hm hm1 ⊢
    rw [hm, hm1, inv_mul_eq_iff_eq_mul₀ hb]
    linear_combination hr


end Real

namespace Real
/-- The leading denominator in the fixed-exponent recurrence is positive. -/
theorem powerLawGegenbauer_recurrence_denominator_pos {α lam : ℝ}
    (hα : -1 < α) (hlam : -(1/2) < lam) (m : ℕ) :
    0 < ((m : ℝ)+1)*((m : ℝ)+2)*((m : ℝ)+2*lam+α+2) := by
  have hn := Nat.cast_nonneg (α := ℝ) m
  exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)


end Real
