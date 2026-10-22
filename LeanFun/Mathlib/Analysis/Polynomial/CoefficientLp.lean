/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Normed.Lp.CoefficientOperators
public import LeanFun.Mathlib.LinearAlgebra.Basis.CoefficientMap

/-! # Polynomial coordinates in square-summable complex coefficient space
Finite coordinates of the original real polynomial bases embed into Mathlib's
lp space. Reference: Olver--Townsend (2013), Sections 2--4.
-/

@[expose] public section
namespace Module.Basis
open Polynomial
open scoped ENNReal

/-- Embed the finite coordinates of a real polynomial basis into complex lp. -/
noncomputable def coefficientLp (b : Basis ℕ ℝ ℝ[X]) :
    ℝ[X] →ₗ[ℝ] lp (fun _ : ℕ ↦ ℂ) 2 where
  toFun p := ⟨fun i ↦ (b.repr p i : ℂ), by
    apply Memℓp.of_exponent_ge (p := 2) (q := 0) _ (by norm_num)
    apply memℓp_zero_iff.mpr
    apply (b.repr p).support.finite_toSet.subset
    intro i hi
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    exact fun hz ↦ hi (by simp [hz])⟩
  map_add' p q := by
    apply lp.ext
    funext i
    change ((b.repr (p + q) i : ℝ) : ℂ) = (b.repr p i : ℂ) + (b.repr q i : ℂ)
    simp
  map_smul' r p := by
    apply lp.ext
    funext i
    change ((b.repr (r • p) i : ℝ) : ℂ) = (r : ℂ) * (b.repr p i : ℂ)
    simp

@[simp] theorem coefficientLp_apply (b : Basis ℕ ℝ ℝ[X]) (p : ℝ[X]) (i : ℕ) :
    b.coefficientLp p i = (b.repr p i : ℂ) := rfl

/-- A polynomial basis vector embeds as the corresponding coordinate vector. -/
@[simp] theorem coefficientLp_basis (b : Basis ℕ ℝ ℝ[X]) (j : ℕ) :
    b.coefficientLp (b j) = lp.single 2 j (1 : ℂ) := by
  ext i
  simp only [coefficientLp_apply, Basis.repr_self, Finsupp.single_apply, lp.single_apply, Pi.single_apply]
  split_ifs <;> simp_all

end Module.Basis
