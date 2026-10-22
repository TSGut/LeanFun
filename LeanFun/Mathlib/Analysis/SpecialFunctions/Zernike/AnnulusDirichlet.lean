/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusOperators
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletMass
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.DirichletEnergy

/-! # Boundary-vanishing annular polynomials and exact Dirichlet operators
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Proposition 15.
-/

@[expose] public section
open Polynomial Module Set
namespace Polynomial

/-- The semiclassical boundary factor is exactly the physical annular boundary factor. -/
theorem annularDirichletWeight_comp {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    (annularDirichletWeight ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩,annulusParameter_ne_zero _⟩).comp (C (annulusParameter ⟨q,ne_of_lt hq.2⟩)*(1-X)) =
      (1-X)*(X-C q) := by
  apply Polynomial.funext
  intro s
  have hq1 : 1-q≠0 := by linarith [hq.2]
  simp [annularDirichletWeight, annulusParameter]
  field_simp
  ring

end Polynomial
namespace MvPolynomial

/-- The polynomial vanishing on both boundary circles of the annulus. -/
noncomputable def annulusBoundaryWeight (q : ℝ) : MvPolynomial (Fin 2) ℝ :=
  (1-(X 0^2+X 1^2))*((X 0^2+X 1^2)-C q)

/-- The boundary factor vanishes at either boundary radius. -/
theorem eval_annulusBoundaryWeight_eq_zero (q : ℝ) (v : Fin 2 → ℝ)
    (hv : v 0^2+v 1^2=q ∨ v 0^2+v 1^2=1) :
    eval v (annulusBoundaryWeight q)=0 := by
  simp only [annulusBoundaryWeight, map_mul, map_sub, map_one, map_add, map_pow, eval_X, eval_C]
  rcases hv with h | h <;> simp [h]

/-- Weighted annular synthesis inserts the physical zero-boundary factor. -/
noncomputable def annulusDirichletLift (q : {q : ℝ // q ≠ 1}) (u : Bool) (m : ℕ) :
    Polynomial ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ :=
  (LinearMap.mulLeft ℝ (annulusBoundaryWeight q)).comp (annulusLift ⟨q,q.property⟩ u m)

/-- Radial and Cartesian boundary weighting agree exactly. -/
theorem annulusLift_dirichletWeight {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (p : Polynomial ℝ) :
    annulusLift ⟨q,ne_of_lt hq.2⟩ u m (annularDirichletWeight ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩,annulusParameter_ne_zero _⟩*p) =
      annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p := by
  simp only [annulusLift, annulusDirichletLift, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.coe_mk, AddHom.coe_mk, diskRadialLift, Polynomial.mul_comp,
    annularDirichletWeight_comp hq, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, Polynomial.eval₂_X, Polynomial.eval₂_C, annulusBoundaryWeight]
  ring

/-- Every polynomial synthesized with the boundary factor satisfies both Dirichlet conditions. -/
theorem eval_annulusDirichletLift_eq_zero (q : {q : ℝ // q ≠ 1}) (u : Bool) (m : ℕ) (p : Polynomial ℝ)
    (v : Fin 2 → ℝ) (hv : v 0^2+v 1^2=q ∨ v 0^2+v 1^2=1) :
    eval v (annulusDirichletLift ⟨q,q.property⟩ u m p)=0 := by
  change eval v (annulusBoundaryWeight q * annulusLift ⟨q,q.property⟩ u m p)=0
  rw [map_mul, eval_annulusBoundaryWeight_eq_zero q v hv, zero_mul]

/-- The tridiagonal radial Dirichlet operator is the actual Cartesian Laplacian. -/
theorem diskLaplacian_annulusDirichletLift {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (p : Polynomial ℝ) :
    diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m p) =
      annulusLift ⟨q,ne_of_lt hq.2⟩ u m (semiclassicalJacobiDirichletMap ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩,annulusParameter_ne_zero _⟩ m p) := by
  rw [← annulusLift_dirichletWeight hq, diskLaplacian_annulusLift,
    ← semiclassicalJacobiDirichletMap_eq _ _ (ne_of_gt
      (lt_trans zero_lt_one (one_lt_annulusParameter hq)))]

/-- Acting on finite coefficients reconstructs the Cartesian Dirichlet Laplacian exactly. -/
theorem annulus_dirichlet_coefficientMap_exact {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (v : ℕ →₀ ℝ) :
    annulusLift ⟨q,ne_of_lt hq.2⟩ u m
      ((semiclassicalJacobiBasis (one_lt_annulusParameter hq)
        (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) m).repr.symm
        ((semiclassicalJacobiBasis (one_lt_annulusParameter hq)
          (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) m).coefficientMap
          (semiclassicalJacobiBasis (one_lt_annulusParameter hq)
            (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) m)
          (semiclassicalJacobiDirichletMap ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩,annulusParameter_ne_zero _⟩ m) v)) =
      diskLaplacian (annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m
        ((semiclassicalJacobiBasis (one_lt_annulusParameter hq)
          (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) m).repr.symm v)) := by
  rw [Basis.repr_symm_coefficientMap, diskLaplacian_annulusDirichletLift hq]

/-- The pentadiagonal mass operator reconstructs the same boundary-weighted polynomial. -/
theorem annulus_dirichlet_mass_coefficientMap_exact {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Bool) (m : ℕ) (v : ℕ →₀ ℝ) :
    annulusLift ⟨q,ne_of_lt hq.2⟩ u m
      ((semiclassicalJacobiBasis (one_lt_annulusParameter hq)
        (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) m).repr.symm
        ((semiclassicalJacobiBasis (one_lt_annulusParameter hq)
          (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) m).coefficientMap
          (semiclassicalJacobiBasis (one_lt_annulusParameter hq)
            (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) m)
          (LinearMap.mulLeft ℝ (annularDirichletWeight ⟨annulusParameter ⟨q,ne_of_lt hq.2⟩,annulusParameter_ne_zero _⟩)) v)) =
      annulusDirichletLift ⟨q,ne_of_lt hq.2⟩ u m
        ((semiclassicalJacobiBasis (one_lt_annulusParameter hq)
          (by norm_num : (-1 : ℝ)<1) (by norm_num : (-1 : ℝ) < 1) m).repr.symm v) := by
  rw [Basis.repr_symm_coefficientMap, LinearMap.mulLeft_apply, annulusLift_dirichletWeight hq]

end MvPolynomial
