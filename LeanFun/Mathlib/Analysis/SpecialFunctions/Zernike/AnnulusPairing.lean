/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.AnnulusMeasure
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Zernike.RadialLift

/-! # Separation of arbitrary polynomial radial modes on annuli
Reference: Papadopoulos–Gutleb–Slevinsky–Olver, Section 4.
-/

public section
open MeasureTheory Set Polynomial
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

/-- Annular pairings separate for arbitrary radial polynomials, even from different families. -/
theorem integralInner_annulusRadialLift {q a b : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ha : -1<a) (hb : -1<b) (u v : Bool) (p z : Polynomial ℝ) (m n : ℕ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (diskRadialLift u p m) (diskRadialLift v z n)) =
      (1/2 : ℝ)*(∫ s : Ioo q 1, (1-(s : ℝ))^a*((s : ℝ)-q)^b*
        (p.eval (s : ℝ)*z.eval (s : ℝ)*Real.sqrt (s : ℝ)^(m+n))) *
      (if u=v ∧ m=n then zernikeAngularNormSq u m else 0) := by
  have hi := integral_zernikeAnnulusMeasure_squaredRadius hq ha hb
    (diskRadialLift u p m * diskRadialLift v z n)
  change (∫ w, eval w (diskRadialLift u p m * diskRadialLift v z n)
    ∂zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) =
    (1/2 : ℝ) * ∫ s : Ioo q 1, (1-(s : ℝ))^a*((s : ℝ)-q)^b *
      ∫ θ in Ioo (-Real.pi) Real.pi,
        eval (![Real.sqrt (s : ℝ)*Real.cos θ, Real.sqrt (s : ℝ)*Real.sin θ] : Fin 2 → ℝ)
          (diskRadialLift u p m * diskRadialLift v z n) at hi
  simp only [map_mul] at hi
  have hin {s : ℝ} (hs : s ∈ Ioo q 1) :
      (∫ θ in Ioo (-Real.pi) Real.pi,
        eval ((![Real.sqrt s*Real.cos θ,Real.sqrt s*Real.sin θ] : Fin 2 → ℝ)) (diskRadialLift u p m)*
        eval ((![Real.sqrt s*Real.cos θ,Real.sqrt s*Real.sin θ] : Fin 2 → ℝ)) (diskRadialLift v z n)) =
      (p.eval (s : ℝ)*z.eval (s : ℝ)*Real.sqrt (s : ℝ)^(m+n))*
        (if u=v ∧ m=n then zernikeAngularNormSq u m else 0) := by
    rw [← integral_zernikeAngular_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with θ
    simp only [eval_diskRadialLift_polar,
      Real.sq_sqrt (show 0≤(s : ℝ) by linarith [hq.1,hs.1]), pow_add]
    ring
  rw [integralInner, hi, mul_assoc (1/2 : ℝ), ← integral_mul_const]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with s
  have hs := s.property
  rw [hin hs]
  ring

/-- Different angular sectors stay orthogonal for every annular radial weight. -/
theorem integralInner_annulusRadialLift_eq_zero_of_angular {q a b : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ha : -1<a) (hb : -1<b)
    {u v : Bool} (p z : Polynomial ℝ) {m n : ℕ} (h : u≠v ∨ m≠n) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (diskRadialLift u p m) (diskRadialLift v z n))=0 := by
  rw [integralInner_annulusRadialLift hq ha hb]
  have hn : ¬(u=v ∧ m=n) := by tauto
  simp [hn]

/-- In a fixed angular sector the squared harmonic supplies the factor s^m. -/
theorem integralInner_annulusRadialLift_same_angular {q a b : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ha : -1<a) (hb : -1<b)
    (u : Bool) (p z : Polynomial ℝ) (m : ℕ) :
    integralInner (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (IntegrablePair.of (zernikeAnnulusMeasure ⟨q,hq.1.le,hq.2⟩ a b) (diskRadialLift u p m) (diskRadialLift u z m)) =
      (1/2 : ℝ)*(∫ s : Ioo q 1, (1-(s : ℝ))^a*((s : ℝ)-q)^b*(s : ℝ)^m*(p.eval (s : ℝ)*z.eval (s : ℝ)))*
        zernikeAngularNormSq u m := by
  rw [integralInner_annulusRadialLift hq ha hb]
  simp only [and_self, ↓reduceIte]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with s
  have hs := s.property
  rw [← two_mul m, pow_mul, Real.sq_sqrt (show 0≤(s : ℝ) by linarith [hq.1,hs.1])]
  ring

end MvPolynomial
