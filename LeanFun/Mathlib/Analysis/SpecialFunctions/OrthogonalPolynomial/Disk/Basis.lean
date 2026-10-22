/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.System
public import LeanFun.Mathlib.Algebra.MvPolynomial.DiskIndex
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.Gram
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Polynomial bases for general Cartesian disk systems

Orthogonality and the total-degree count give bases of every finite degree space.
Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, Chapter 3.
-/

@[expose] public section
open MeasureTheory Set Module
namespace MvPolynomial.CartesianDiskSystem
variable {μ ν : Measure ℝ} (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)

/-- The Cartesian family restricted to a finite total-degree space. -/
noncomputable def degreeFamily (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    restrictTotalDegree (Fin 2) ℝ N :=
  ⟨S.polynomial (d.1 0+d.1 1) (d.1 1),
    (mem_restrictTotalDegree (Fin 2) N _).mpr
      ((S.totalDegree_polynomial_le (by omega)).trans
        (by simpa only [sum_exponents_fin_two] using d.2))⟩

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (hz : ∀ᵐ z ∂ν, z ∈ Icc (-1 : ℝ) 1)

include hx hz

/-- The Cartesian family is independent before any basis is chosen. -/
theorem linearIndependent :
    LinearIndependent ℝ (fun i : Σ n : ℕ, Fin (n+1) => S.polynomial i.1 i.2) := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := integralBilinForm (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν))
      (hasFiniteMoments_cartesianDiskMeasure hx hz))
  · intro i j hij
    apply S.integralInner_polynomial_eq_zero hx (by omega) (by omega)
    intro h
    apply hij
    have hn := congrArg Prod.fst h
    have hk := congrArg Prod.snd h
    rcases i with ⟨n,k⟩
    rcases j with ⟨m,l⟩
    dsimp at hn hk
    subst m
    congr 1
    exact Fin.ext hk
  · intro i
    change integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) _ _) ≠ 0
    rw [S.integralInner_polynomial_self hx]
    exact one_ne_zero

/-- Independence in each finite degree subspace. -/
theorem linearIndependent_degreeFamily (N : ℕ) :
    LinearIndependent ℝ (S.degreeFamily N) := by
  have h := ((S.linearIndependent hx hz).comp _ diskIndex_injective).comp
    (fun d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} => d.1) Subtype.val_injective
  exact LinearIndependent.of_comp (restrictTotalDegree (Fin 2) ℝ N).subtype h

/-- The general Cartesian family is a basis of the full finite degree space. -/
noncomputable def degreeBasis (N : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := by
  classical
  let b : Basis {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N} ℝ
      (restrictTotalDegree (Fin 2) ℝ N) := basisRestrictSupport ℝ _
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}
  exact basisOfLinearIndependentOfCardEqFinrank' (S.degreeFamily N)
    (S.linearIndependent_degreeFamily hx hz N) (Module.finrank_eq_card_basis b).symm

/-- The basis members are the explicit Cartesian polynomials. -/
@[simp] theorem degreeBasis_apply (N : ℕ)
    (d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    (S.degreeBasis hx hz N d : MvPolynomial (Fin 2) ℝ) =
      S.polynomial (d.1 0+d.1 1) (d.1 1) := by
  simp [degreeBasis, degreeFamily]

/-- Each finite Cartesian basis has identity integral Gram matrix. -/
theorem integralGram_degreeBasis (N : ℕ) :
    integralGram (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν))
      (fun i => (S.degreeBasis hx hz N i : MvPolynomial (Fin 2) ℝ)) = 1 := by
  classical
  ext i j
  simp only [integralGram, degreeBasis_apply, Matrix.one_apply]
  by_cases hij : i=j
  · subst j
    rw [S.integralInner_polynomial_self hx, ite_eq_left rfl]
  · rw [ite_eq_right hij]
    apply S.integralInner_polynomial_eq_zero hx (by omega) (by omega)
    intro h
    apply hij
    apply Subtype.ext
    have hn := congrArg Prod.fst h
    have hk := congrArg Prod.snd h
    ext t
    fin_cases t <;> dsimp at hn hk ⊢ <;> omega

/-- Coordinates in the Cartesian basis are polynomial integral pairings. -/
theorem degreeBasis_repr (N : ℕ) (p : restrictTotalDegree (Fin 2) ℝ N)
    (i : {d : Fin 2 →₀ ℕ // d.sum (fun _ e => e) ≤ N}) :
    (S.degreeBasis hx hz N).repr p i =
      integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν)) (S.polynomial (i.1 0+i.1 1) (i.1 1)) p) := by
  rw [basis_repr_eq_integralInner _ (hasFiniteMoments_cartesianDiskMeasure hx hz)
    _ (S.integralGram_degreeBasis hx hz N)]
  simp only [integralInner, degreeBasis_apply]

end MvPolynomial.CartesianDiskSystem
