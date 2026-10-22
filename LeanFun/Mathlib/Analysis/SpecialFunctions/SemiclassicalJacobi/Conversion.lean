/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Basis
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Weight
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionGram
public import LeanFun.Mathlib.LinearAlgebra.Matrix.Banded
import Mathlib.Tactic.ComputeDegree

/-! # Banded semiclassical parameter conversion
Integer raising is polynomial measure modification. The normalized connection
is a positive upper triangular Gram factor. Reference: Papadopoulos–Gutleb–
Slevinsky–Olver, Section 3, and Gutleb–Olver–Slevinsky, measure conversion.
-/

@[expose] public section
open MeasureTheory Module Set
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- The polynomial density associated with three integer parameter shifts. -/
noncomputable def semiclassicalJacobiShiftDensity (t : ℝ) (a b c : ℕ) : ℝ[X] :=
  X^a*(1-X)^b*(C t-X)^c

/-- The modifying density has the expected degree bound. -/
theorem natDegree_semiclassicalJacobiShiftDensity_le (t : ℝ) (a b c : ℕ) :
    (semiclassicalJacobiShiftDensity t a b c).natDegree ≤ a+b+c := by
  unfold semiclassicalJacobiShiftDensity
  compute_degree

/-- The modifying polynomial is nonnegative almost everywhere on the source measure. -/
theorem ae_nonneg_semiclassicalJacobiShiftDensity {t : ℝ} (ht : 1 < t)
    (α β γ : ℝ) (a b c : ℕ) :
    ∀ᵐ x ∂semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ,
      0 ≤ (semiclassicalJacobiShiftDensity t a b c).eval x := by
  filter_upwards [ae_mem_Ioo_semiclassicalJacobiMeasure ⟨t, by assumption⟩ α β γ] with x hx
  simp only [semiclassicalJacobiShiftDensity, eval_mul, eval_pow, eval_sub, eval_one, eval_C, eval_X]
  exact mul_nonneg (mul_nonneg (pow_nonneg hx.1.le _)
    (pow_nonneg (by linarith [hx.2]) _)) (pow_nonneg (by linarith [hx.2]) _)

/-- Classical parameter-shift transport for a bundled integrable input. -/
theorem integral_semiclassicalJacobi_shift_integrable {t : ℝ} (ht : 1 < t)
    (α β γ : ℝ) (a b c : ℕ)
    (f : IntegrableInput (semiclassicalJacobiMeasure ⟨t, ht⟩ (α+a) (β+b) (γ+c))) :
    Integrable (fun x ↦ (semiclassicalJacobiShiftDensity t a b c).eval x * f.val x)
      (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ) ∧
    (∫ x, f.val x ∂semiclassicalJacobiMeasure ⟨t, ht⟩ (α+a) (β+b) (γ+c)) =
      ∫ x, (semiclassicalJacobiShiftDensity t a b c).eval x * f.val x
        ∂semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ := by
  have hi : Integrable
      (fun x ↦ (semiclassicalJacobiShiftDensity t a b c).eval x * f.val x)
      (semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ) := by
    rw [integrable_semiclassicalJacobiMeasure_iff]
    have h := (integrable_semiclassicalJacobiMeasure_iff _ _ _ _ _).1 f.property
    convert h using 1
    ext x
    rw [semiclassicalJacobiWeight_add_nat]
    simp only [semiclassicalJacobiShiftDensity, eval_mul, eval_pow, eval_sub,
      eval_X, eval_C, eval_one]
    ring
  refine ⟨hi, ?_⟩
  rw [integral_semiclassicalJacobiMeasure ⟨t, ht⟩ (α+a) (β+b) (γ+c) f,
    integral_semiclassicalJacobiMeasure ⟨t, ht⟩ α β γ ⟨_, hi⟩]
  congr 1
  ext x
  rw [semiclassicalJacobiWeight_add_nat]
  simp only [semiclassicalJacobiShiftDensity, eval_mul, eval_pow, eval_sub,
    eval_X, eval_C, eval_one]
  ring

/-- The connection matrix between two positive orthonormal semiclassical bases. -/
noncomputable def semiclassicalJacobiConnection {t α β α' β' : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα' : -1 < α') (hβ' : -1 < β') (γ' : ℝ) : Matrix ℕ ℕ ℝ :=
  (semiclassicalJacobiBasis ht hα' hβ' γ').toMatrix (semiclassicalJacobiBasis ht hα hβ γ)

/-- Raising by (a,b,c) gives an upper connection of bandwidth at most a+b+c. -/
theorem semiclassicalJacobiConnection_eq_zero {t α β γ : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (a b c : ℕ)
    (hαa : -1 < α+a) (hβb : -1 < β+b) (n m : ℕ)
    (hgap : n < m ∨ m+(a+b+c) < n) :
    semiclassicalJacobiConnection ht hα hβ γ hαa hβb (γ+c) m n = 0 := by
  rw [semiclassicalJacobiConnection, Basis.toMatrix_apply, semiclassicalJacobiBasis_apply,
    semiclassicalJacobiBasis_repr]
  have hQ := (semiclassicalJacobiSequence_spec ht hαa hβb (γ+c)).1
  have hP := (semiclassicalJacobiSequence_spec ht hα hβ γ).1
  have hM := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ) ht hα hβ
  have hT := hasFiniteMoments_semiclassicalJacobiMeasure (γ := γ+c) ht hαa hβb
  rcases hgap with hgap | hgap
  · exact hQ.integralInner_eq_zero_of_degree_lt hT
      (by simpa only [Sequence.degree_eq, Nat.cast_lt] using hgap)
  · rw [integralInner_comm]
    have he := (integral_semiclassicalJacobi_shift_integrable ht α β γ a b c
      ⟨_, hT.integrable_mul (semiclassicalJacobiSequence ht hαa hβb (γ+c) m)
        (semiclassicalJacobiSequence ht hα hβ γ n)⟩).2
    simp only [integralInner] at ⊢
    erw [he]
    have hd : (semiclassicalJacobiShiftDensity t a b c *
        semiclassicalJacobiSequence ht hαa hβb (γ+c) m).natDegree < n :=
      natDegree_mul_le.trans_lt (by
        rw [Sequence.natDegree_eq]
        have := natDegree_semiclassicalJacobiShiftDensity_le t a b c
        omega)
    have hz := hP.integralInner_eq_zero_of_degree_lt hM
      (degree_le_natDegree.trans_lt (by exact_mod_cast hd))
    simpa only [integralInner, eval_mul, mul_assoc] using hz

/-- Every leading section is the transpose-product factor of the target Gram matrix. -/
theorem semiclassicalJacobiConnection_gram {t α β α' β' : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα' : -1 < α') (hβ' : -1 < β') (γ' : ℝ) (N : ℕ) :
    Matrix.of (fun i j : Fin N ↦ integralInner (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α' β' γ') (IntegrablePair.of (semiclassicalJacobiMeasure ⟨t, by assumption⟩ α' β' γ') (semiclassicalJacobiSequence ht hα hβ γ i) (semiclassicalJacobiSequence ht hα hβ γ j))) =
      (Matrix.of (fun i j : Fin N ↦ semiclassicalJacobiConnection ht hα hβ γ hα' hβ' γ' i j)).transpose *
        Matrix.of (fun i j : Fin N ↦ semiclassicalJacobiConnection ht hα hβ γ hα' hβ' γ' i j) := by
  simpa only [semiclassicalJacobiConnection, Basis.toMatrix_apply, semiclassicalJacobiBasis_apply,
    semiclassicalJacobiBasis, Sequence.basis_eq_self] using
    (semiclassicalJacobiSequence_spec ht hα' hβ' γ').1.connection_gram
      (hasFiniteMoments_semiclassicalJacobiMeasure ht hα' hβ')
      (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα' hβ')
      (fun n ↦ isUnit_iff_ne_zero.mpr ((semiclassicalJacobiSequence_spec ht hα' hβ' γ').2.1 n).ne')
      (semiclassicalJacobiSequence ht hα hβ γ)
      (fun n ↦ by simpa only [integralInner_self] using
        (semiclassicalJacobiSequence_spec ht hα' hβ' γ').2.2 n) N

/-- Every leading connection section is upper triangular in degree order. -/
theorem semiclassicalJacobiConnection_upperTriangular {t α β α' β' : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα' : -1 < α') (hβ' : -1 < β') (γ' : ℝ) (N : ℕ) :
    (Matrix.of (fun i j : Fin N ↦ semiclassicalJacobiConnection ht hα hβ γ hα' hβ' γ' i j)).IsUpperTriangular := by
  simpa only [semiclassicalJacobiConnection, Basis.toMatrix_apply, semiclassicalJacobiBasis_apply,
    semiclassicalJacobiBasis, Sequence.basis_eq_self] using
    (semiclassicalJacobiSequence_spec ht hα' hβ' γ').1.connection_upperTriangular
      (hasFiniteMoments_semiclassicalJacobiMeasure ht hα' hβ')
      (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα' hβ')
      (fun n ↦ isUnit_iff_ne_zero.mpr ((semiclassicalJacobiSequence_spec ht hα' hβ' γ').2.1 n).ne')
      (semiclassicalJacobiSequence ht hα hβ γ) N

/-- Positive normalization makes each connection diagonal entry positive. -/
theorem semiclassicalJacobiConnection_diag_pos {t α β α' β' : ℝ} (ht : 1 < t)
    (hα : -1 < α) (hβ : -1 < β) (γ : ℝ)
    (hα' : -1 < α') (hβ' : -1 < β') (γ' : ℝ) (n : ℕ) :
    0 < semiclassicalJacobiConnection ht hα hβ γ hα' hβ' γ' n n := by
  simpa only [semiclassicalJacobiConnection, Basis.toMatrix_apply, semiclassicalJacobiBasis_apply,
    semiclassicalJacobiBasis, Sequence.basis_eq_self] using
    (semiclassicalJacobiSequence_spec ht hα' hβ' γ').1.connection_diag_pos
      (hasFiniteMoments_semiclassicalJacobiMeasure ht hα' hβ')
      (hasPositiveDefiniteIntegral_semiclassicalJacobiMeasure ht hα' hβ')
      (fun n ↦ isUnit_iff_ne_zero.mpr ((semiclassicalJacobiSequence_spec ht hα' hβ' γ').2.1 n).ne')
      (semiclassicalJacobiSequence ht hα hβ γ)
      (semiclassicalJacobiSequence_spec ht hα hβ γ).2.1
      (semiclassicalJacobiSequence_spec ht hα' hβ' γ').2.1 n

end Polynomial
