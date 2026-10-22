/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.ExtensionPairing

/-! # Single-degree-block support of Jacobi-to-Proriol extension

Reference: Gutleb–Olver, arXiv:1906.03907, Section 3.1.
-/

public section
open Polynomial
namespace MvPolynomial

/-- A shifted `(1,0)` Jacobi mode extends entirely within its own total-degree
block, including all positive inner degrees. -/
theorem proriolExtensionCoefficients_shiftedJacobi_eq_zero_of_degree_ne (n : ℕ)
    (i : Σ m : ℕ, Fin (m+1)) (hi : i.1 ≠ n) :
    proriolExtensionCoefficients n (shiftedJacobi 1 0 n)
      (natDegree_shiftedJacobi_le 1 0 n) i = 0 := by
  by_cases hn : n < i.1
  · exact proriolExtensionCoefficients_eq_zero _ _ _ _ hn
  have hn : i.1 < n := by omega
  let d : Fin 2 →₀ ℕ := Finsupp.single 0 (i.1-i.2.1)+Finsupp.single 1 i.2.1
  have hd0 : d 0 = i.1-i.2.1 := by simp [d]
  have hd1 : d 1 = i.2.1 := by simp [d]
  have hd : d 0+d 1 = i.1 := by rw [hd0, hd1]; omega
  let e : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ n} :=
    ⟨d, by rw [sum_exponents_fin_two, hd]; omega⟩
  have he : (⟨e.1 0+e.1 1, ⟨e.1 1, by omega⟩⟩ : Σ m : ℕ, Fin (m+1)) = i := by
    apply Sigma.ext hd
    exact (Fin.heq_ext_iff (congrArg (fun t : ℕ ↦ t+1) hd)).mpr hd1
  rw [← he, proriolExtensionCoefficients_eq_moment]
  have hz := integralInner_extendY_shiftedJacobi_eq_zero
    (proriol 0 0 0 (d 0+d 1) (d 1))
    ((totalDegree_proriol_le 0 0 0 (by omega)).trans_lt (by rw [hd]; exact hn))
  rw [integralInner_proriolMeasure_zero] at hz
  change (-1 : ℝ)^(d 0)*proriolTriangleMoment
    (triangleExtendY (shiftedJacobi 1 0 n)*proriol 0 0 0 (d 0+d 1) (d 1)) / _ = 0
  rw [hz, mul_zero, zero_div]

end MvPolynomial
