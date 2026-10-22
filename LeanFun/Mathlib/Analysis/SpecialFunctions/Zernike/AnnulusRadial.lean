/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.SemiclassicalJacobi.Sequence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The annular radial bridge to semiclassical Jacobi polynomials
Write q=rho² for the squared inner radius and t=1/(1-q). The variable
x=t(1-r²) transports annular radial pairings to x^a(1-x)^b(t-x)^m dx.
The angular harmonics contribute r^(2m), so m is precisely the third
semiclassical parameter. Reference: Papadopoulos–Gutleb–Slevinsky–Olver,
Section 4, equations (34)–(36).
-/

@[expose] public section
open MeasureTheory Set Real
attribute [local instance] Measure.Subtype.measureSpace
namespace Polynomial

/-- The external semiclassical singularity determined by the squared inner radius. -/
noncomputable def annulusParameter (q : {q : ℝ // q ≠ 1}) : ℝ := (1-(q : ℝ))⁻¹

/-- The nondegenerate radial parameter is nonzero. -/
theorem annulusParameter_ne_zero (q : {q : ℝ // q ≠ 1}) :
    annulusParameter q ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (Ne.symm q.property))

/-- A nondegenerate annulus puts the third singularity strictly beyond one. -/
theorem one_lt_annulusParameter {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    1 < annulusParameter ⟨q, ne_of_lt hq.2⟩ := by
  unfold annulusParameter
  rw [one_lt_inv₀ (by linarith [hq.2])]
  linarith [hq.1]

/-- The affine coordinate has the normalization required at both annular endpoints. -/
theorem annulusParameter_mul (q : ℝ) (hq : q≠1) : annulusParameter ⟨q, hq⟩*(1-q)=1 := by
  unfold annulusParameter
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hq))

/-- The three semiclassical factors become the outer, inner and angular radial weights. -/
private theorem semiclassicalJacobiWeight_annulus_rpow {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (a b : ℝ) (m : ℕ) {s : ℝ} (hs : s ∈ Ioo q 1) :
    (((annulusParameter ⟨q, ne_of_lt hq.2⟩*(1-s)) : ℝ) ^ (a) * (1 - ((annulusParameter ⟨q, ne_of_lt hq.2⟩*(1-s)) : ℝ)) ^ (b) * (((annulusParameter ⟨q, ne_of_lt hq.2⟩) : ℝ) - ((annulusParameter ⟨q, ne_of_lt hq.2⟩*(1-s)) : ℝ)) ^ (m : ℝ)) =
      (annulusParameter ⟨q, ne_of_lt hq.2⟩)^(a+b+(m : ℝ)) * ((1-s)^a*(s-q)^b*s^m) := by
  have ht : 0 < annulusParameter ⟨q, ne_of_lt hq.2⟩ := lt_trans zero_lt_one (one_lt_annulusParameter hq)
  have he := annulusParameter_mul q (ne_of_lt hq.2)
  have h1 : 1-annulusParameter ⟨q, ne_of_lt hq.2⟩*(1-s)=annulusParameter ⟨q, ne_of_lt hq.2⟩*(s-q) := by nlinarith [he]
  have h2 : annulusParameter ⟨q, ne_of_lt hq.2⟩-annulusParameter ⟨q, ne_of_lt hq.2⟩*(1-s)=annulusParameter ⟨q, ne_of_lt hq.2⟩*s := by ring
  rw [h1, h2, mul_rpow ht.le (by linarith [hs.2]),
    mul_rpow ht.le (by linarith [hs.1]), mul_rpow ht.le (by linarith [hq.1,hs.1]),
    rpow_add ht, rpow_add ht, rpow_natCast, rpow_natCast]
  ring

/-- The annular weight identity evaluated at a typed interior squared radius. -/
theorem semiclassicalJacobiWeight_annulus (q : Ioo (0 : ℝ) 1) (a b : ℝ) (m : ℕ)
    (s : Ioo (q : ℝ) 1) :
    (semiclassicalJacobiWeight ⟨annulusParameter ⟨q, ne_of_lt q.property.2⟩, one_lt_annulusParameter q.property⟩ a b m
      ⟨annulusParameter ⟨q, ne_of_lt q.property.2⟩ * (1 - (s : ℝ)), by
        have ht : 0 < annulusParameter ⟨q, ne_of_lt q.property.2⟩ := lt_trans zero_lt_one (one_lt_annulusParameter q.property)
        have he := annulusParameter_mul q (ne_of_lt q.property.2)
        constructor
        · exact mul_pos ht (sub_pos.mpr s.property.2)
        · nlinarith [mul_pos ht (sub_pos.mpr s.property.1)]⟩ : ℝ) =
      (annulusParameter ⟨q, ne_of_lt q.property.2⟩) ^ (a + b + (m : ℝ)) *
        ((1 - (s : ℝ)) ^ a * ((s : ℝ) - q) ^ b * (s : ℝ) ^ m) := by
  exact semiclassicalJacobiWeight_annulus_rpow q.property a b m s.property

/-- The radial annular polynomials are the semiclassical family at angular parameter m. -/
noncomputable def zernikeAnnulusRadial {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (k m : ℕ) : Polynomial ℝ :=
  (semiclassicalJacobiSequence (one_lt_annulusParameter hq) ha hb m k).comp
    (C (annulusParameter ⟨q, ne_of_lt hq.2⟩)*(1-X))

/-- Evaluation uses precisely the annular squared-radius coordinate. -/
theorem eval_zernikeAnnulusRadial {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (k m : ℕ) (s : ℝ) :
    (zernikeAnnulusRadial hq ha hb k m).eval s =
      (semiclassicalJacobiSequence (one_lt_annulusParameter hq) ha hb m k).eval
        (annulusParameter ⟨q, ne_of_lt hq.2⟩*(1-s)) := by
  simp [zernikeAnnulusRadial, eval_comp]

/-- Every integrable semiclassical input remains integrable under the annular
change of variables, including integrable endpoint singularities (PGSO Section 4). -/
theorem integrable_semiclassicalJacobiMeasure_annulus (q : Ioo (0 : ℝ) 1)
    (a b : ℝ) (m : ℕ)
    (f : IntegrableInput (semiclassicalJacobiMeasure
      ⟨annulusParameter ⟨q, ne_of_lt q.property.2⟩, one_lt_annulusParameter q.property⟩ a b m)) :
    Integrable (fun s : Ioo (q : ℝ) 1 ↦ (1 - (s : ℝ)) ^ a * ((s : ℝ) - q) ^ b *
      (s : ℝ) ^ m * f.val (annulusParameter ⟨q, ne_of_lt q.property.2⟩ * (1 - (s : ℝ)))) volume := by
  let t := annulusParameter ⟨q, ne_of_lt q.property.2⟩
  have ht : 0 < t := lt_trans zero_lt_one (one_lt_annulusParameter q.property)
  have he := annulusParameter_mul q (ne_of_lt q.property.2)
  have hq : (t - 1) / t = (q : ℝ) := by
    apply (div_eq_iff ht.ne').2
    dsimp [t]
    nlinarith [he]
  have hs := (integrable_semiclassicalJacobiMeasure_iff
    ⟨t, one_lt_annulusParameter q.property⟩ a b m f.val).1 f.property
  let G : ℝ → ℝ := fun x ↦ if h : x ∈ Ioo (0 : ℝ) 1 then
    (semiclassicalJacobiWeight ⟨t, one_lt_annulusParameter q.property⟩ a b m ⟨x,h⟩ : ℝ) * f.val x
    else 0
  have hi : IntervalIntegrable G volume 0 1 := by
    rw [intervalIntegrable_iff, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc]
    apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).2
    convert hs using 1
    funext x
    exact dite_eq_left x.property
  have hc := ((hi.comp_sub_left t).comp_mul_left (c := t)).symm
  simp only [sub_zero, div_self ht.ne', hq] at hc
  rw [intervalIntegrable_iff, uIoc_of_le q.property.2.le,
    IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc] at hc
  have hj := (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).1 hc
  have heq (s : Ioo (q : ℝ) 1) : G (t - t * (s : ℝ)) =
      t ^ (a+b+(m : ℝ)) * ((1-(s : ℝ))^a*((s : ℝ)-q)^b*(s : ℝ)^m *
        f.val (t*(1-(s : ℝ)))) := by
    have hx : t*(1-(s : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact mul_pos ht (sub_pos.mpr s.property.2)
      · dsimp [t] at *
        nlinarith [mul_pos ht (sub_pos.mpr s.property.1)]
    rw [show t-t*(s : ℝ)=t*(1-(s : ℝ)) by ring]
    simp only [G, dite_eq_left hx]
    rw [semiclassicalJacobiWeight_annulus q a b m s]
    ring
  change Integrable (fun s : Ioo (q : ℝ) 1 ↦ G (t-t*(s : ℝ))) volume at hj
  convert hj.const_mul (t ^ (a+b+(m : ℝ)))⁻¹ using 1
  funext s
  rw [heq, ← mul_assoc, inv_mul_cancel₀ (rpow_pos_of_pos ht _).ne', one_mul]

/-- Classical radial transport for a bundled integrable input (PGSO Section 4). -/
theorem integral_semiclassicalJacobiMeasure_annulus (q : Ioo (0 : ℝ) 1)
    (a b : ℝ) (m : ℕ)
    (f : IntegrableInput (semiclassicalJacobiMeasure
      ⟨annulusParameter ⟨q, ne_of_lt q.property.2⟩, one_lt_annulusParameter q.property⟩ a b m)) :
    ∫ x, f.val x ∂semiclassicalJacobiMeasure
      ⟨annulusParameter ⟨q, ne_of_lt q.property.2⟩, one_lt_annulusParameter q.property⟩ a b m =
      (annulusParameter ⟨q, ne_of_lt q.property.2⟩) ^ (a + b + (m : ℝ) + 1) *
        ∫ s : Ioo (q : ℝ) 1, (1 - (s : ℝ)) ^ a * ((s : ℝ) - q) ^ b *
          (s : ℝ) ^ m * f.val (annulusParameter ⟨q, ne_of_lt q.property.2⟩ * (1 - (s : ℝ))) := by
  let t := annulusParameter ⟨q, ne_of_lt q.property.2⟩
  have ht : 0 < t := lt_trans zero_lt_one (one_lt_annulusParameter q.property)
  have he := annulusParameter_mul q (ne_of_lt q.property.2)
  let G : ℝ → ℝ := fun x ↦ if h : x ∈ Ioo (0 : ℝ) 1 then
    (semiclassicalJacobiWeight ⟨t, one_lt_annulusParameter q.property⟩ a b m ⟨x,h⟩ : ℝ) * f.val x
    else 0
  have hG : (∫ x, f.val x ∂semiclassicalJacobiMeasure
      ⟨t, one_lt_annulusParameter q.property⟩ a b m) = ∫ x in 0..1, G x := by
    rw [integral_semiclassicalJacobiMeasure _ _ _ _ f,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← restrict_Ioo_eq_restrict_Ioc, ← integral_subtype_comap measurableSet_Ioo G]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [G, dite_eq_left x.property]
    rfl
  have h0 : -t*1-(-t)=0 := by ring
  have h1 : -t*(q : ℝ)-(-t)=1 := by dsimp [t]; nlinarith [he]
  have hi := intervalIntegral.smul_integral_comp_mul_sub
    (a := (q : ℝ)) (b := 1) G (-t) (-t)
  rw [h0,h1,intervalIntegral.integral_symm (0 : ℝ) 1] at hi
  simp only [smul_eq_mul, neg_mul, neg_inj] at hi
  rw [hG, ← hi, intervalIntegral.integral_of_le q.property.2.le,
    ← restrict_Ioo_eq_restrict_Ioc, ← integral_subtype_comap measurableSet_Ioo]
  have heq (s : Ioo (q : ℝ) 1) : G (-(t*(s : ℝ))-(-t)) =
      t ^ (a+b+(m : ℝ)) * ((1-(s : ℝ))^a*((s : ℝ)-q)^b*(s : ℝ)^m *
        f.val (t*(1-(s : ℝ)))) := by
    have hx : t*(1-(s : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact mul_pos ht (sub_pos.mpr s.property.2)
      · dsimp [t] at *
        nlinarith [mul_pos ht (sub_pos.mpr s.property.1)]
    rw [show -(t*(s : ℝ))-(-t)=t*(1-(s : ℝ)) by ring]
    simp only [G, dite_eq_left hx]
    rw [semiclassicalJacobiWeight_annulus q a b m s]
    ring
  change t * (∫ s : Ioo (q : ℝ) 1, G (-(t*(s : ℝ))-(-t))) =
    t^(a+b+(m : ℝ)+1) * ∫ s : Ioo (q : ℝ) 1,
      (1-(s : ℝ))^a*((s : ℝ)-q)^b*(s : ℝ)^m * f.val (t*(1-(s : ℝ)))
  simp_rw [heq]
  rw [integral_const_mul, rpow_add ht (a+b+(m : ℝ)) 1, rpow_one]
  ring

/-- Exact annular radial orthogonality and norms, with the full geometric scale. -/
theorem integral_zernikeAnnulusRadial_mul {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (k l m : ℕ) :
    ∫ s : Ioo q 1, (1-(s : ℝ))^a*((s : ℝ)-q)^b*(s : ℝ)^m*
      ((zernikeAnnulusRadial hq ha hb k m).eval (s : ℝ) *
        (zernikeAnnulusRadial hq ha hb l m).eval (s : ℝ)) =
      ((annulusParameter ⟨q, ne_of_lt hq.2⟩)^(a+b+(m : ℝ)+1))⁻¹ * (if k=l then 1 else 0) := by
  let Q := semiclassicalJacobiSequence (one_lt_annulusParameter hq) ha hb (m : ℝ)
  have hQ := semiclassicalJacobiSequence_spec (one_lt_annulusParameter hq) ha hb (m : ℝ)
  have ho : (∫ x, (Q k).eval x*(Q l).eval x
      ∂semiclassicalJacobiMeasure ⟨annulusParameter ⟨q, ne_of_lt hq.2⟩, one_lt_annulusParameter hq⟩ a b m) = if k=l then 1 else 0 := by
    by_cases h : k=l
    · subst l
      simpa only [↓reduceIte, ← pow_two] using hQ.2.2 k
    · simpa only [ite_eq_right h] using hQ.1.orthogonal k l h
  have hi := (hasFiniteMoments_semiclassicalJacobiMeasure
    (γ := (m : ℝ)) (one_lt_annulusParameter hq) ha hb).integrable_mul (Q k) (Q l)
  rw [integral_semiclassicalJacobiMeasure_annulus ⟨q,hq⟩ a b m ⟨_,hi⟩] at ho
  simp only [eval_zernikeAnnulusRadial]
  change (∫ s : Ioo q 1, (1-(s : ℝ))^a*((s : ℝ)-q)^b*(s : ℝ)^m*
    ((Q k).eval (annulusParameter ⟨q, ne_of_lt hq.2⟩*(1-(s : ℝ)))*(Q l).eval (annulusParameter ⟨q, ne_of_lt hq.2⟩*(1-(s : ℝ))))) = _
  have ht : 0 < annulusParameter ⟨q, ne_of_lt hq.2⟩ := lt_trans zero_lt_one (one_lt_annulusParameter hq)
  rw [← ho, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]


end Polynomial
