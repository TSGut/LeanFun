/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusPairing
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.Index
import Mathlib.Tactic.ComputeDegree

/-! # Real two-dimensional Zernike annular polynomials
The radial polynomials retain positive semiclassical leading coefficients in
x=t(1-r²). Their real angular phases and total-degree ordering match the disk API.
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

@[expose] public section
open MeasureTheory Polynomial Set
namespace MvPolynomial

/-- A Cartesian polynomial annular mode, built from the established radial family. -/
noncomputable def zernikeAnnulusMode {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (u : Bool) (k m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  diskRadialLift u (zernikeAnnulusRadial hq ha hb k m) m

/-- The annular radial polynomial has degree at most its sequence index. -/
theorem natDegree_zernikeAnnulusRadial_le {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (k m : ℕ) :
    (zernikeAnnulusRadial hq ha hb k m).natDegree ≤ k := by
  unfold zernikeAnnulusRadial
  apply natDegree_comp_le.trans
  rw [(semiclassicalJacobiSequence (one_lt_annulusParameter hq) ha hb (m : ℝ)).natDegree_eq]
  have hd : (Polynomial.C (annulusParameter ⟨q,ne_of_lt hq.2⟩)*(1-Polynomial.X) : Polynomial ℝ).natDegree ≤ 1 := by
    compute_degree
  simpa using Nat.mul_le_mul_left k hd

/-- Annular modes belong to the same total-degree spaces as their disk counterparts. -/
theorem totalDegree_zernikeAnnulusMode_le {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (u : Bool) (k m : ℕ) :
    (zernikeAnnulusMode hq ha hb u k m).totalDegree ≤ 2*k+m :=
  (totalDegree_diskRadialLift_le _ _ _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (natDegree_zernikeAnnulusRadial_le hq ha hb k m)) m)

/-- Exact same-sector annular pairings, including their geometric scale. -/
theorem integralInner_zernikeAnnulusMode_same_angular {q a b : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ha : -1<a) (hb : -1<b) (u : Bool) (k l m : ℕ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (zernikeAnnulusMode hq ha hb u k m) (zernikeAnnulusMode hq ha hb u l m)) =
      (1/2 : ℝ)*(((annulusParameter ⟨q,ne_of_lt hq.2⟩)^(a+b+(m : ℝ)+1))⁻¹*(if k=l then 1 else 0))*
        zernikeAngularNormSq u m := by
  dsimp only [zernikeAnnulusMode]
  rw [integralInner_annulusRadialLift_same_angular hq ha hb, integral_zernikeAnnulusRadial_mul]

/-- Distinct annular modes are orthogonal in the standard weighted planar measure. -/
theorem integralInner_zernikeAnnulusMode_eq_zero {q a b : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ha : -1<a) (hb : -1<b)
    {u v : Bool} {k m l n : ℕ} (hne : (u,k,m)≠(v,l,n)) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (zernikeAnnulusMode hq ha hb u k m) (zernikeAnnulusMode hq ha hb v l n))=0 := by
  by_cases hu : u=v
  · subst v
    by_cases hm : m=n
    · subst n
      rw [integralInner_zernikeAnnulusMode_same_angular hq ha hb]
      have hk : k≠l := by aesop
      simp [hk]
    · exact integralInner_annulusRadialLift_eq_zero_of_angular hq ha hb _ _ (Or.inr hm)
  · exact integralInner_annulusRadialLift_eq_zero_of_angular hq ha hb _ _ (Or.inl hu)

/-- Every retained real annular mode has a strictly positive squared norm. -/
theorem integral_sq_zernikeAnnulusMode_pos {q a b : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ha : -1<a) (hb : -1<b)
    (u : Bool) (k m : ℕ) (hm : u=true → m≠0) :
    0 < ∫ v, (eval v (zernikeAnnulusMode hq ha hb u k m))^2 ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b := by
  rw [← integralInner_self _ _ (h := (hasFiniteMoments_zernikeAnnulusMeasure hq ha hb).integrable_mul _ _), integralInner_zernikeAnnulusMode_same_angular hq ha hb]
  have ht : 0<annulusParameter ⟨q,ne_of_lt hq.2⟩ := lt_trans zero_lt_one (one_lt_annulusParameter hq)
  have hang : 0<zernikeAngularNormSq u m := by
    cases u <;> simp only [zernikeAngularNormSq, Bool.false_eq_true, ↓reduceIte] at *
    · split <;> positivity
    · simp [hm, Real.pi_pos]
  simp only [↓reduceIte, mul_one]
  positivity

/-- Total-degree ordering shared with the real disk family. -/
noncomputable def zernikeAnnulus {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (n j : ℕ) : MvPolynomial (Fin 2) ℝ :=
  zernikeAnnulusMode hq ha hb (zernikeSine n j) (zernikeRadialDegree n j) (zernikeFrequency n j)

/-- The ordered annular polynomial lies in the stated degree space. -/
theorem totalDegree_zernikeAnnulus_le {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) {n j : ℕ} (hj : j≤n) :
    (zernikeAnnulus hq ha hb n j).totalDegree ≤ n := by
  have hd := totalDegree_zernikeAnnulusMode_le hq ha hb
    (zernikeSine n j) (zernikeRadialDegree n j) (zernikeFrequency n j)
  simpa only [zernikeAnnulus, (zernike_index_spec hj).1] using hd

/-- Distinct valid degree indices are orthogonal. -/
theorem integralInner_zernikeAnnulus_eq_zero {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) {n j m l : ℕ} (hj : j≤n) (hl : l≤m) (hne : (n,j)≠(m,l)) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (zernikeAnnulus hq ha hb n j) (zernikeAnnulus hq ha hb m l))=0 :=
  integralInner_zernikeAnnulusMode_eq_zero hq ha hb (fun h ↦ hne (zernike_index_injective hj hl h))

/-- Valid ordered annular polynomials have positive squared norms. -/
theorem integral_sq_zernikeAnnulus_pos {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) {n j : ℕ} (hj : j≤n) :
    0 < ∫ v, (eval v (zernikeAnnulus hq ha hb n j))^2 ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b :=
  integral_sq_zernikeAnnulusMode_pos hq ha hb _ _ _ (zernike_index_spec hj).2

end MvPolynomial
