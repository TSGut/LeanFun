/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Matrix.CholeskyPath
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

/-! # Finite exceptional parameters for inverse matrix pencils
Every nontrivial entry of F(1+tK)^{-1}E is a rational function of t. Its
exceptional real parameters form a finite set. Reference: adjugate formula.
-/

@[expose] public section
open Polynomial Filter
namespace Matrix
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- The polynomial matrix underlying an affine scalar pencil. -/
noncomputable def polynomialPencil (K : Matrix ι ι ℝ) : Matrix ι ι ℝ[X] :=
  1 + (Polynomial.X : ℝ[X]) • K.map (Polynomial.C : ℝ → ℝ[X])

/-- Evaluating the polynomial pencil recovers the real matrix. -/
theorem eval_polynomialPencil (K : Matrix ι ι ℝ) (t : ℝ) :
    (Polynomial.evalRingHom t).mapMatrix (polynomialPencil K) = 1 + t • K := by
  ext i j
  change (Polynomial.evalRingHom t)
    ((if i = j then 1 else 0) + (Polynomial.X : ℝ[X]) * Polynomial.C (K i j)) =
      (if i = j then 1 else 0) + t * K i j
  by_cases hij : i = j <;> simp [hij] <;> ring

/-- The adjugate sandwich is polynomial in the pencil parameter. -/
noncomputable def inversePencilNumerator (K : Matrix ι ι ℝ)
    (F : Matrix κ ι ℝ) (E : Matrix ι κ ℝ) (i j : κ) : ℝ[X] :=
  (F.map Polynomial.C * (polynomialPencil K).adjugate * E.map Polynomial.C) i j

/-- Evaluation of the numerator is the actual adjugate sandwich. -/
theorem eval_inversePencilNumerator (K : Matrix ι ι ℝ)
    (F : Matrix κ ι ℝ) (E : Matrix ι κ ℝ) (i j : κ) (t : ℝ) :
    (inversePencilNumerator K F E i j).eval t = (F * (1 + t • K).adjugate * E) i j := by
  change ((F.map Polynomial.C * (polynomialPencil K).adjugate * E.map Polynomial.C).map
    (Polynomial.evalRingHom t)) i j = _
  rw [Matrix.map_mul, Matrix.map_mul]
  change ((F.map Polynomial.C).map (Polynomial.evalRingHom t) *
    (Polynomial.evalRingHom t).mapMatrix (polynomialPencil K).adjugate *
    (E.map Polynomial.C).map (Polynomial.evalRingHom t)) i j = _
  rw [RingHom.map_adjugate, eval_polynomialPencil]
  simp [Matrix.map_map, Function.comp_def]


/-- Parameters at which the affine pencil is invertible. -/
abbrev InvertiblePencilParameter (K : Matrix ι ι ℝ) :=
  {t : ℝ // IsUnit (1 + t • K)}

/-- The classical inverse of an affine matrix pencil. -/
noncomputable def inversePencil (K : Matrix ι ι ℝ)
    (t : InvertiblePencilParameter K) : Matrix ι ι ℝ :=
  ↑(t.property.unit⁻¹)

/-- Internal bridge to the imported matrix inverse, on its invertible domain. -/
theorem inversePencil_eq_inv (K : Matrix ι ι ℝ) (t : InvertiblePencilParameter K) :
    inversePencil K t = (1 + (t : ℝ) • K)⁻¹ := by
  simp only [inversePencil, Matrix.coe_units_inv, IsUnit.unit_spec]

/-- The inverse solves the two matrix inverse equations. -/
theorem inversePencil_mul (K : Matrix ι ι ℝ) (t : InvertiblePencilParameter K) :
    inversePencil K t * (1 + (t : ℝ) • K) = 1 ∧
      (1 + (t : ℝ) • K) * inversePencil K t = 1 := by
  change (↑(t.property.unit⁻¹) : Matrix ι ι ℝ) * (1 + (t : ℝ) • K) = 1 ∧
    (1 + (t : ℝ) • K) * (↑(t.property.unit⁻¹) : Matrix ι ι ℝ) = 1
  exact ⟨by simpa only [IsUnit.unit_spec] using Units.inv_mul t.property.unit,
    by simpa only [IsUnit.unit_spec] using Units.mul_inv t.property.unit⟩

/-- The determinant detects exactly the classical parameter domain. -/
theorem isUnit_pencil_iff_det_ne_zero (K : Matrix ι ι ℝ) (t : ℝ) :
    IsUnit (1 + t • K) ↔ (polynomialPencil K).det.eval t ≠ 0 := by
  have hd := ((Polynomial.evalRingHom t).map_det (polynomialPencil K)).trans
    (congrArg Matrix.det (eval_polynomialPencil K t))
  change (polynomialPencil K).det.eval t = (1 + t • K).det at hd
  rw [hd, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- Only finitely many real parameters are singular. -/
theorem eventually_cofinite_isUnit_pencil (K : Matrix ι ι ℝ) :
    ∀ᶠ t : ℝ in Filter.cofinite, IsUnit (1 + t • K) := by
  have hd : (polynomialPencil K).det ≠ 0 := by
    intro hz
    have h := congrArg (fun p : ℝ[X] ↦ p.eval 0) hz
    have he := ((Polynomial.evalRingHom (0 : ℝ)).map_det (polynomialPencil K)).trans
      (congrArg Matrix.det (eval_polynomialPencil K 0))
    simp only [zero_smul, add_zero, Matrix.det_one] at he
    change (polynomialPencil K).det.eval 0 = 1 at he
    simp [he] at h
  filter_upwards [Polynomial.eventually_cofinite_not_isRoot hd] with t ht
  exact (isUnit_pencil_iff_det_ne_zero K t).2 ht

/-- An inverse entry equals its polynomial numerator divided by the nonzero determinant. -/
theorem inversePencil_sandwich_eq (K : Matrix ι ι ℝ)
    (F : Matrix κ ι ℝ) (E : Matrix ι κ ℝ) (i j : κ)
    (t : InvertiblePencilParameter K) :
    (F * inversePencil K t * E) i j =
      ((polynomialPencil K).det.eval (t : ℝ))⁻¹ *
        (inversePencilNumerator K F E i j).eval (t : ℝ) := by
  have hd : (polynomialPencil K).det.eval (t : ℝ) = (1 + (t : ℝ) • K).det := by
    exact ((Polynomial.evalRingHom (t : ℝ)).map_det _).trans
      (congrArg Matrix.det (eval_polynomialPencil K t))
  rw [inversePencil_eq_inv, hd, eval_inversePencilNumerator, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- A nonzero classical inverse sandwich stays nonzero outside a finite exceptional set. -/
theorem eventually_cofinite_inversePencil_sandwich_ne_zero (K : Matrix ι ι ℝ)
    (F : Matrix κ ι ℝ) (E : Matrix ι κ ℝ) (i j : κ)
    (hn : ∃ t : InvertiblePencilParameter K, (F * inversePencil K t * E) i j ≠ 0) :
    ∀ᶠ t : ℝ in Filter.cofinite, ∃ ht : IsUnit (1 + t • K),
      (F * inversePencil K ⟨t, ht⟩ * E) i j ≠ 0 := by
  have hp : inversePencilNumerator K F E i j ≠ 0 := by
    obtain ⟨t, ht⟩ := hn
    intro hz
    apply ht
    rw [inversePencil_sandwich_eq, hz]
    simp
  filter_upwards [eventually_cofinite_isUnit_pencil K,
    Polynomial.eventually_cofinite_not_isRoot hp] with t ht hp
  refine ⟨ht, ?_⟩
  rw [inversePencil_sandwich_eq]
  exact mul_ne_zero (inv_ne_zero ((isUnit_pencil_iff_det_ne_zero K t).1 ht)) hp

end Matrix
