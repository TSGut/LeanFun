/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/

module

public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.Product
public import LeanFun.Mathlib.Analysis.InnerProductSpace.Toeplitz.ContinuousSymbol

/-! # Laurent symbols and their continuous Toeplitz realization

The Fourier realization agrees with the shift construction. Laurent symbols
are uniformly dense among continuous symbols. Reference: Böttcher–Silbermann,
Introduction to Large Truncated Toeplitz Matrices, Chapter 1.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace AddCircle
variable {T : ℝ} [Fact (0 < T)]
local notation "H" => lp (fun _ : ℕ ↦ ℂ) 2

/-- Realization of a Laurent polynomial on a circle with nonzero signed period. -/
def laurentSymbol {T : {T : ℝ // T ≠ 0}} : LaurentPolynomial ℂ →ₗ[ℂ] C(AddCircle (T : ℝ), ℂ) where
  toFun p := Finsupp.linearCombination ℂ fourier p.coeff
  map_add' p q := by simp
  map_smul' a p := by simp

/-- A Laurent monomial realizes as the corresponding Fourier monomial. -/
theorem laurentSymbol_single {T : {T : ℝ // T ≠ 0}} (k : ℤ) (a : ℂ) :
    laurentSymbol (T := T) (AddMonoidAlgebra.single k a) = a • fourier k := by
  change Finsupp.linearCombination ℂ fourier (Finsupp.single k a) = _
  simp

/-- Fourier monomial compression is precisely the signed shift. -/
theorem continuousToeplitz_fourier (k : ℤ) :
    continuousToeplitz (fourier (T := T) k) = lp.laurentShiftL2 k := by
  apply lp.continuousLinearMap_ext_single
  intro j
  apply lp.ext
  funext i
  rw [continuousToeplitz_entry, lp.laurentShiftL2_single_entry, fourierCoeff_fourier]
  simp only [Pi.single_apply, eq_comm]

/-- The continuous-symbol and Laurent-polynomial Toeplitz constructions agree. -/
theorem continuousToeplitz_laurentSymbol (p : LaurentPolynomial ℂ) :
    continuousToeplitz (laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩) p) = lp.laurentToeplitz p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact (continuousToeplitzCLM (T := T)).map_zero
  | add p q hp hq => simp only [map_add, continuousToeplitz_add, hp, hq]
  | single k a =>
    rw [laurentSymbol_single, continuousToeplitz_smul, continuousToeplitz_fourier,
      lp.laurentToeplitz_single]

/-- Laurent symbol realization respects multiplication. -/
theorem laurentSymbol_mul {T : {T : ℝ // T ≠ 0}} (p q : LaurentPolynomial ℂ) :
    laurentSymbol (T := T) (p*q) = laurentSymbol (T := T) p*laurentSymbol (T := T) q := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p r hp hr => simp only [add_mul, map_add, hp, hr]
  | single k a =>
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add q r hq hr => simp only [mul_add, map_add, hq, hr]
    | single l b =>
      rw [AddMonoidAlgebra.single_mul_single]
      simp only [laurentSymbol_single]
      ext x
      simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul, fourier_add]
      ring

/-- The constant-one Laurent polynomial realizes as the constant-one symbol. -/
theorem laurentSymbol_one {T : {T : ℝ // T ≠ 0}} : laurentSymbol (T := T) (1 : LaurentPolynomial ℂ) = 1 := by
  change laurentSymbol (T := T) (AddMonoidAlgebra.single (0 : ℤ) (1 : ℂ)) = 1
  rw [laurentSymbol_single, one_smul]
  ext x
  exact fourier_zero

/-- Circle realization preserves powers of Laurent polynomials. -/
theorem laurentSymbol_pow {T : {T : ℝ // T ≠ 0}} (p : LaurentPolynomial ℂ) (n : ℕ) :
    laurentSymbol (T := T) (p^n) = (laurentSymbol (T := T) p)^n := by
  induction n with
  | zero => simp only [pow_zero, laurentSymbol_one]
  | succ n ih => rw [pow_succ, laurentSymbol_mul, ih, pow_succ]

/-- Laurent-polynomial symbols have the sharp uniform-norm operator bound. -/
theorem norm_laurentToeplitz_le_symbol (p : LaurentPolynomial ℂ) :
    ‖lp.laurentToeplitz p‖ ≤ ‖laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩) p‖ := by
  rw [← continuousToeplitz_laurentSymbol (T := T)]
  exact norm_continuousToeplitz_le _

/-- Laurent symbols are uniformly dense among continuous circle functions. -/
theorem denseRange_laurentSymbol : DenseRange (laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩)) := by
  have hs : Submodule.span ℂ (Set.range (fourier (T := T))) ≤
      LinearMap.range (laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩)) := by
    apply Submodule.span_le.mpr
    rintro f ⟨k, rfl⟩
    exact ⟨AddMonoidAlgebra.single k 1, by rw [laurentSymbol_single, one_smul]⟩
  have ht : (LinearMap.range (laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩))).topologicalClosure = ⊤ := by
    apply top_le_iff.mp
    rw [← span_fourier_closure_eq_top (T := T)]
    exact Submodule.topologicalClosure_mono hs
  intro f
  change f ∈ ((LinearMap.range (laurentSymbol (T := ⟨T, (Fact.out : 0 < T).ne'⟩))).topologicalClosure : Set _)
  rw [ht]
  trivial

/-- Continuous-symbol products agree with symbol multiplication modulo compact operators. -/
theorem isCompactOperator_continuousToeplitz_mul_sub (f g : C(AddCircle T, ℂ)) :
    IsCompactOperator (fun u : H ↦
      (continuousToeplitz f * continuousToeplitz g - continuousToeplitz (f*g)) u) := by
  refine (denseRange_laurentSymbol (T := T)).induction_on₂
    (p := fun f g ↦ IsCompactOperator (fun u : H ↦
      (continuousToeplitz f * continuousToeplitz g - continuousToeplitz (f*g)) u)) ?_ ?_ f g
  · change IsClosed ((fun p : C(AddCircle T, ℂ) × C(AddCircle T, ℂ) ↦
        continuousToeplitzCLM p.1 * continuousToeplitzCLM p.2 -
          continuousToeplitzCLM (p.1*p.2)) ⁻¹'
        {A : H →L[ℂ] H | IsCompactOperator A})
    exact isClosed_setOfPred_isCompactOperator.preimage (by fun_prop)
  · intro p q
    rw [← laurentSymbol_mul, continuousToeplitz_laurentSymbol,
      continuousToeplitz_laurentSymbol, continuousToeplitz_laurentSymbol]
    exact lp.isCompactOperator_laurentToeplitz_mul_sub p q

end AddCircle
