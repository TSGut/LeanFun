/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusLaplacian
public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Conversion

/-! # Exact coefficient actions in annular angular sectors
Parameter conversion and Laplacians act on finite radial coefficients without
coupling different angular frequencies or phases. Reference:
Papadopoulos–Gutleb–Slevinsky–Olver, Section 4, Propositions 13 and 14.
-/

@[expose] public section
open Polynomial Module Set
namespace MvPolynomial

/-- Lift a semiclassical polynomial through the annular affine coordinate and angular harmonic. -/
noncomputable def annulusLift (q : {q : ℝ // q ≠ 1}) (u : Bool) (m : ℕ) :
    Polynomial ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ where
  toFun p := diskRadialLift u (p.comp (Polynomial.C (annulusParameter q)*(1-Polynomial.X))) m
  map_add' p z := by
    cases u <;> simp [diskRadialLift, Polynomial.add_comp, Polynomial.eval₂_add, add_mul]
  map_smul' c p := by
    cases u <;> simp [diskRadialLift, Polynomial.smul_eq_C_mul, Polynomial.mul_comp,
      Polynomial.eval₂_mul, MvPolynomial.smul_eq_C_mul, mul_assoc]

/-- The established annular modes are the images of the semiclassical basis. -/
theorem annulusLift_basis {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (u : Bool) (k m : ℕ) :
    annulusLift ⟨q,ne_of_lt hq.2⟩ u m (semiclassicalJacobiBasis (one_lt_annulusParameter hq) ha hb m k) =
      zernikeAnnulusMode hq ha hb u k m := by
  simp [annulusLift, semiclassicalJacobiBasis_apply, zernikeAnnulusMode, zernikeAnnulusRadial]

/-- Changing radial parameters reconstructs the very same Cartesian polynomial. -/
theorem annulus_conversion_coefficientMap_exact {q a b a' b' : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ha : -1<a) (hb : -1<b)
    (ha' : -1<a') (hb' : -1<b') (u : Bool) (m : ℕ) (v : ℕ →₀ ℝ) :
    annulusLift ⟨q,ne_of_lt hq.2⟩ u m ((semiclassicalJacobiBasis (one_lt_annulusParameter hq) ha' hb' m).repr.symm
      ((semiclassicalJacobiBasis (one_lt_annulusParameter hq) ha hb m).coefficientMap
        (semiclassicalJacobiBasis (one_lt_annulusParameter hq) ha' hb' m) LinearMap.id v)) =
      annulusLift ⟨q,ne_of_lt hq.2⟩ u m ((semiclassicalJacobiBasis (one_lt_annulusParameter hq) ha hb m).repr.symm v) := by
  rw [Basis.repr_symm_coefficientMap, LinearMap.id_apply]

/-- Integer endpoint raising has radial bandwidth at most the sum of the shifts. -/
theorem annulus_conversion_eq_zero {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (r s m : ℕ)
    (har : -1<a+r) (hbs : -1<b+s) (k l : ℕ) (hgap : k<l ∨ l+(r+s)<k) :
    semiclassicalJacobiConnection (one_lt_annulusParameter hq) ha hb m har hbs m l k = 0 := by
  simpa only [Nat.cast_zero, add_zero] using
    semiclassicalJacobiConnection_eq_zero (γ := (m : ℝ)) (one_lt_annulusParameter hq)
      ha hb r s 0 har hbs k l (by simpa only [add_zero] using hgap)

/-- The banded radial Laplacian is the Cartesian Laplacian of every lifted polynomial. -/
theorem diskLaplacian_annulusLift (q : {q : ℝ // q ≠ 1}) (u : Bool) (m : ℕ) (p : Polynomial ℝ) :
    diskLaplacian (annulusLift q u m p) =
      annulusLift q u m (semiclassicalJacobiAnnularLaplacianMap (annulusParameter q) m p) := by
  change diskLaplacian (diskRadialLift u _ m) = diskRadialLift u _ m
  rw [diskLaplacian_diskRadialLift, annularLaplacian_comp]

/-- The sparse coefficient Laplacian reconstructs the Cartesian result exactly. -/
theorem annulus_laplacian_coefficientMap_exact {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (ha2 : -1<(a+1)+1) (hb2 : -1<(b+1)+1)
    (u : Bool) (m : ℕ) (v : ℕ →₀ ℝ) :
    annulusLift ⟨q,ne_of_lt hq.2⟩ u m ((semiclassicalJacobiBasis (one_lt_annulusParameter hq) ha2 hb2 m).repr.symm
      ((semiclassicalJacobiBasis (one_lt_annulusParameter hq) ha hb m).coefficientMap
        (semiclassicalJacobiBasis (one_lt_annulusParameter hq) ha2 hb2 m)
        (semiclassicalJacobiAnnularLaplacianMap (annulusParameter ⟨q,ne_of_lt hq.2⟩) m) v)) =
      diskLaplacian (annulusLift ⟨q,ne_of_lt hq.2⟩ u m
        ((semiclassicalJacobiBasis (one_lt_annulusParameter hq) ha hb m).repr.symm v)) := by
  rw [Basis.repr_symm_coefficientMap, diskLaplacian_annulusLift]

end MvPolynomial
