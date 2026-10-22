/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusBasis
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusOperators

/-! # Polynomial spanning by annular angular sectors
Finite total-degree bases allow linear identities to be checked sector by sector.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

public section
open Polynomial Set Module
namespace MvPolynomial

/-- A submodule containing every annular radial lift contains every Cartesian polynomial. -/
theorem eq_top_of_annulusLift_mem {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (K : Submodule ℝ (MvPolynomial (Fin 2) ℝ))
    (hK : ∀ u m p, annulusLift ⟨q,ne_of_lt hq.2⟩ u m p ∈ K) : K = ⊤ := by
  classical
  apply top_unique
  intro p hp
  let v : restrictTotalDegree (Fin 2) ℝ p.totalDegree :=
    ⟨p, (mem_restrictTotalDegree (Fin 2) _ _).mpr le_rfl⟩
  let b := zernikeAnnulusDegreeBasis hq (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0) p.totalDegree
  have he := congrArg (fun w : restrictTotalDegree (Fin 2) ℝ p.totalDegree ↦
    (w : MvPolynomial (Fin 2) ℝ)) (b.linearCombination_repr v)
  change ((∑ i ∈ (b.repr v).support, (b.repr v) i • b i :
    restrictTotalDegree (Fin 2) ℝ p.totalDegree) : MvPolynomial (Fin 2) ℝ) = p at he
  simp only [Submodule.coe_sum, Submodule.coe_smul] at he
  rw [← he]
  apply K.sum_mem
  intro i hi
  apply K.smul_mem
  simp only [b, zernikeAnnulusDegreeBasis_apply, zernikeAnnulus]
  rw [← annulusLift_basis]
  exact hK _ _ _

end MvPolynomial
