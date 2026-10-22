/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerPolynomial
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Gegenbauer.Operators
public import LeanFun.Mathlib.Algebra.Polynomial.Sequence.Comrade
/-! # Classical compatible polynomial operators
The full operator has whole-family admissibility; an individual coefficient
column requires only its own nonsingular finite prefix. Polynomial integration
uses the bundled weighted input. Reference: Gutleb--Carrillo--Olver,
arXiv:2011.00045, Section2.
-/
@[expose] public noncomputable section
open Polynomial Set
namespace Real
open MeasureTheory
/-- Whole-family data with a genuine Gegenbauer polynomial basis. -/
abbrev PowerLawOperatorData := {p : PowerLawFamilyData // -(1/2) < p.lam ∧ p.lam ≠ 0}
/-- Finite-column data preserve every mode whose own recurrence prefix exists. -/
abbrev PowerLawColumnData (n : ℕ) := {p : PowerLawRecurrenceData n // -(1/2) < p.lam ∧ p.lam ≠ 0}
def PowerLawOperatorData.ofIntegrable (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (hzero : lam.val ≠ 0) : PowerLawOperatorData :=
  ⟨.ofIntegrable α lam, lam.property, hzero⟩
def PowerLawOperatorData.atDegree (p : PowerLawOperatorData) (n : ℕ) : PowerLawColumnData n :=
  ⟨p.val.atDegree n, p.property⟩
/-- Polynomial inputs use the already constructed integrable weighted domain. -/
def PowerLawInput.gegenbauerPolynomial (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (p : ℝ[X]) : PowerLawInput α.val x.val :=
  .gegenbauerContinuous α lam x ⟨fun y ↦ p.eval y.val, p.continuous.comp continuous_subtype_val⟩
/-- The classical weighted integral as a polynomial linear functional. -/
def powerLawPolynomial (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := powerLawIntegral (.gegenbauerPolynomial α lam x p)
  map_add' p q := by
    have hp := (PowerLawInput.gegenbauerPolynomial α lam x p).property
    have hq := (PowerLawInput.gegenbauerPolynomial α lam x q).property
    simpa only [powerLawIntegral, PowerLawInput.gegenbauerPolynomial,
      PowerLawInput.gegenbauerContinuous, ContinuousMap.coe_mk, eval_add, mul_add] using integral_add hp hq
  map_smul' c p := by
    change powerLawIntegral (.gegenbauerPolynomial α lam x (c • p)) =
      c * powerLawIntegral (.gegenbauerPolynomial α lam x p)
    unfold powerLawIntegral PowerLawInput.gegenbauerPolynomial PowerLawInput.gegenbauerContinuous
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [ContinuousMap.coe_mk, eval_smul, smul_eq_mul]
    ring
/-- An exact polynomial operator on the full classical family domain. -/
def powerLawGegenbauerOperator (p : PowerLawOperatorData) (k : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (gegenbauerBasis p.property.1 p.property.2).constr ℝ
    (fun n ↦ powerLawGegenbauerPolynomial k n (p.val.atDegree n))
@[simp] theorem powerLawGegenbauerOperator_gegenbauer (p : PowerLawOperatorData) (k n : ℕ) :
    powerLawGegenbauerOperator p k (gegenbauer p.val.lam n) =
      powerLawGegenbauerPolynomial k n (p.val.atDegree n) := by
  rw [← gegenbauerBasis_apply p.property.1 p.property.2 n]
  exact Module.Basis.constr_basis _ _ _ _
/-- Each coefficient column is defined on its own finite-prefix domain. -/
def powerLawGegenbauerCoefficients {n : ℕ} (p : PowerLawColumnData n) (k : ℕ) : ℕ →₀ ℝ :=
  (gegenbauerBasis p.property.1 p.property.2).repr (powerLawGegenbauerPolynomial k n p.val)
theorem powerLawGegenbauerCoefficients_eq_zero_of_degree {n : ℕ}
    (p : PowerLawColumnData n) (k j : ℕ) (hj : n+2*k < j) :
    powerLawGegenbauerCoefficients p k j = 0 := by
  apply (gegenbauerSequence p.property.1 p.property.2).basis_repr_eq_zero_of_degree_lt
    (n := j) (hj := le_rfl)
  exact degree_le_natDegree.trans_lt (by exact_mod_cast
    (natDegree_powerLawGegenbauerPolynomial_le k n p.val).trans_lt hj)
/-- Evaluation of the assembled operator equals the classical integral functional. -/
theorem eval_powerLawGegenbauerOperator (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (hzero : lam.val ≠ 0) {k : ℕ}
    (hk : lam.val+α.val/2 = k) (x : Ioo (-1 : ℝ) 1) (p : ℝ[X]) :
    (powerLawGegenbauerOperator (.ofIntegrable α lam hzero) k p).eval x.val =
      powerLawPolynomial α lam x p := by
  have h : (aeval x.val : ℝ[X] →ₐ[ℝ] ℝ).toLinearMap.comp
      (powerLawGegenbauerOperator (.ofIntegrable α lam hzero) k) =
      powerLawPolynomial α lam x := by
    apply (gegenbauerBasis lam.property hzero).ext
    intro n
    erw [gegenbauerBasis_apply]
    change (powerLawGegenbauerOperator (.ofIntegrable α lam hzero) k
      (gegenbauer lam.val n)).eval x.val =
      powerLawPolynomial α lam x (gegenbauer lam.val n)
    erw [powerLawGegenbauerOperator_gegenbauer]
    change (powerLawGegenbauerPolynomial k n (.ofIntegrable α lam n)).eval x.val =
      powerLawIntegral (.gegenbauerMode α lam x n)
    exact eval_powerLawGegenbauerPolynomial α lam hk x n
  exact congrArg (fun L : ℝ[X] →ₗ[ℝ] ℝ ↦ L p) h

end Real
namespace Real

end Real
namespace Real
/-- Pointwise characterization of polynomial weighted inputs. -/
theorem PowerLawInput.gegenbauerPolynomial_apply (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (p : ℝ[X]) (y : PowerLawDomain x.val) :
    (PowerLawInput.gegenbauerPolynomial α lam x p).val y =
      (Polynomial.gegenbauerWeight lam.val ⟨y.val,y.property.1⟩ : ℝ)*p.eval y.val := rfl
/-- The polynomial functional is exactly the classical weighted integral. -/
theorem powerLawPolynomial_apply (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) (p : ℝ[X]) :
    powerLawPolynomial α lam x p =
      powerLawIntegral (.gegenbauerPolynomial α lam x p) := rfl
/-- Finite columns agree with the matrix of the whole-family operator. -/
theorem powerLawGegenbauerCoefficients_eq_operator (p : PowerLawOperatorData) (k n : ℕ) :
    powerLawGegenbauerCoefficients (p.atDegree n) k =
      (gegenbauerBasis p.property.1 p.property.2).repr
        (powerLawGegenbauerOperator p k (gegenbauer p.val.lam n)) := by
  rw [powerLawGegenbauerOperator_gegenbauer]
  rfl
end Real
