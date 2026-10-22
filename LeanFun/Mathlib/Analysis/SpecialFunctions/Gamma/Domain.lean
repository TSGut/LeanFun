/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Gamma on its classical domain
The poles are excluded in the argument type. Euler integrals use strictly
positive real integration variables. Reference: DLMF 5.2.1 and 5.5.1.
-/
@[expose] public noncomputable section
open MeasureTheory Set Polynomial
namespace Complex

/-- The complex plane with the Gamma poles removed. -/
abbrev GammaPoint := {z : ℂ // ∀ n : ℕ, z ≠ -(n : ℂ)}

/-- Gamma evaluated only at a non-pole. -/
def GammaOn (z : GammaPoint) : ℂ := Gamma z.val

/-- The right half-plane is contained in the classical Gamma domain. -/
def GammaPoint.ofRePos (z : ℂ) (hz : 0 < z.re) : GammaPoint := by
  refine ⟨z, fun n he ↦ ?_⟩
  have h := congrArg Complex.re he
  simp only [neg_re, natCast_re] at h
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Shifting a non-pole by a natural number remains in the classical domain. -/
def GammaPoint.addNat (z : GammaPoint) (n : ℕ) : GammaPoint := by
  refine ⟨z.val + n, fun m he ↦ z.property (m + n) ?_⟩
  push_cast
  linear_combination he

@[simp] theorem GammaPoint.addNat_val (z : GammaPoint) (n : ℕ) :
    (z.addNat n).val = z.val + n := rfl

/-- A natural shift takes every classical argument into the Euler half-plane. -/
theorem GammaPoint.exists_positive_shift (z : GammaPoint) :
    ∃ n : ℕ, 0 < (z.val + n).re := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-z.val.re)
  refine ⟨n, ?_⟩
  simp only [add_re, natCast_re]
  linarith

/-- The classical normalization at one. -/
theorem GammaOn_one : GammaOn (GammaPoint.ofRePos 1 (by simp)) = 1 := Gamma_one

/-- Gamma has no zeros on its classical domain. -/
theorem GammaOn_ne_zero (z : GammaPoint) : GammaOn z ≠ 0 := Gamma_ne_zero z.property

/-- Euler's integral is integrable and equals the classical Gamma value. -/
theorem GammaOn_euler (z : GammaPoint) (hz : 0 < z.val.re) :
    Integrable (fun t : Ioi (0 : ℝ) ↦ (Real.exp (-t.val) : ℂ) * (t.val : ℂ) ^ (z.val - 1)) (Measure.comap Subtype.val volume) ∧
    GammaOn z = ∫ t : Ioi (0 : ℝ), (Real.exp (-t.val) : ℂ) * (t.val : ℂ) ^ (z.val - 1) ∂Measure.comap Subtype.val volume := by
  constructor
  · exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp (GammaIntegral_convergent hz)
  · rw [GammaOn, Gamma_eq_integral hz, GammaIntegral]
    exact (integral_subtype_comap (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (fun t : ℝ ↦ (Real.exp (-t) : ℂ) * (t : ℂ) ^ (z.val - 1))).symm

/-- The functional equation involves only genuine Gamma values. -/
theorem GammaOn_add_one (z : GammaPoint) :
    GammaOn (z.addNat 1) = z.val * GammaOn z := by
  simpa only [GammaOn, GammaPoint.addNat_val, Nat.cast_one] using
    Gamma_add_one z.val (by simpa using z.property 0)

/-- The shifted Gamma ratio equals the ascending Pochhammer polynomial. -/
theorem GammaOn_add_nat_div (z : GammaPoint) (n : ℕ) :
    GammaOn (z.addNat n) / GammaOn z = (ascPochhammer ℂ n).eval z.val :=
  Gamma_add_nat_div_Gamma_eq z.val z.property

/-- Every non-pole is characterized by a shifted convergent Euler integral. -/
theorem GammaOn_euler_shift (z : GammaPoint) (n : ℕ) (hn : 0 < (z.val + n).re) :
    (ascPochhammer ℂ n).eval z.val ≠ 0 ∧
    Integrable (fun t : Ioi (0 : ℝ) ↦ (Real.exp (-t.val) : ℂ) *
      (t.val : ℂ) ^ (z.val + n - 1)) (Measure.comap Subtype.val volume) ∧
    GammaOn z = (∫ t : Ioi (0 : ℝ), (Real.exp (-t.val) : ℂ) *
      (t.val : ℂ) ^ (z.val + n - 1) ∂Measure.comap Subtype.val volume) /
        (ascPochhammer ℂ n).eval z.val := by
  have h := (div_eq_iff (GammaOn_ne_zero z)).mp (GammaOn_add_nat_div z n)
  have hp : (ascPochhammer ℂ n).eval z.val ≠ 0 := by
    intro he
    apply GammaOn_ne_zero (z.addNat n)
    rw [h, he, zero_mul]
  have hi := GammaOn_euler (z.addNat n) hn
  simp only [GammaPoint.addNat_val] at hi
  refine ⟨hp, hi.1, ?_⟩
  rw [← hi.2]
  apply (eq_div_iff hp).mpr
  simpa only [mul_comm] using h.symm

end Complex
namespace Real

/-- The real line with the Gamma poles removed. -/
abbrev GammaPoint := {x : ℝ // ∀ n : ℕ, x ≠ -(n : ℝ)}

/-- Real Gamma evaluated only at a non-pole. -/
def GammaOn (x : GammaPoint) : ℝ := Gamma x.val

/-- Positive reals are in the classical Gamma domain. -/
def GammaPoint.ofPos (x : ℝ) (hx : 0 < x) : GammaPoint :=
  ⟨x, fun n h ↦ by linarith [Nat.cast_nonneg (α := ℝ) n]⟩

/-- A real non-pole gives a complex non-pole. -/
def GammaPoint.toComplex (x : GammaPoint) : Complex.GammaPoint := by
  refine ⟨x.val, fun n h ↦ x.property n ?_⟩
  exact_mod_cast h

/-- Real Gamma has no zeros on its classical domain. -/
theorem GammaOn_ne_zero (x : GammaPoint) : GammaOn x ≠ 0 := Gamma_ne_zero x.property

/-- Positive inputs have positive Gamma value. -/
theorem GammaOn_pos (x : GammaPoint) (hx : 0 < x.val) : 0 < GammaOn x := Gamma_pos_of_pos hx

/-- The real Euler integral uses only positive real powers and is integrable. -/
theorem GammaOn_euler (x : GammaPoint) (hx : 0 < x.val) :
    Integrable (fun t : Ioi (0 : ℝ) ↦ exp (-t.val) * t.val ^ (x.val - 1)) (Measure.comap Subtype.val volume) ∧
    GammaOn x = ∫ t : Ioi (0 : ℝ), exp (-t.val) * t.val ^ (x.val - 1) ∂Measure.comap Subtype.val volume := by
  constructor
  · exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp (GammaIntegral_convergent hx)
  · rw [GammaOn, Gamma_eq_integral hx]
    exact (integral_subtype_comap (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (fun t : ℝ ↦ exp (-t) * t ^ (x.val - 1))).symm

/-- Real and complex Gamma agree on real non-poles. -/
theorem GammaOn_toComplex (x : GammaPoint) :
    Complex.GammaOn x.toComplex = (GammaOn x : ℂ) := Complex.Gamma_ofReal x.val

end Real

open Filter
open scoped Topology
namespace Complex

/-- The entire reciprocal Gamma function: its zeros at the poles of Gamma are
classical extension values, and inversion is used only at nonzero Gamma values. -/
def reciprocalGamma (z : ℂ) : ℂ := by
  classical
  exact if h : ∀ n : ℕ, z ≠ -(n : ℂ) then (GammaOn ⟨z, h⟩)⁻¹ else 0


/-- The reciprocal is an actual multiplicative inverse at every non-pole. -/
theorem reciprocalGamma_mul_GammaOn (z : GammaPoint) : reciprocalGamma z.val * GammaOn z = 1 := by
  classical
  rw [reciprocalGamma, dite_eq_left z.property]
  exact inv_mul_cancel₀ (GammaOn_ne_zero z)

/-- The entire reciprocal has precisely the nonpositive integers as zeros. -/
theorem reciprocalGamma_eq_zero_iff (z : ℂ) :
    reciprocalGamma z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  classical
  by_cases hp : ∀ n : ℕ, z ≠ -(n : ℂ)
  · rw [reciprocalGamma, dite_eq_left hp]
    constructor
    · intro hz
      exact False.elim ((GammaOn_ne_zero ⟨z,hp⟩) (inv_eq_zero.mp hz))
    · rintro ⟨n,hn⟩
      exact False.elim (hp n hn)
  · rw [reciprocalGamma, dite_eq_right hp]
    constructor
    · intro _
      simpa only [not_forall,not_not] using hp
    · intro _
      rfl

private theorem shifted_reciprocal (n : ℕ) (z : ℂ) (hz : 0 < (z+n).re) :
    reciprocalGamma z = (ascPochhammer ℂ n).eval z /
      GammaOn (GammaPoint.ofRePos (z+n) hz) := by
  classical
  by_cases hp : ∀ k : ℕ, z ≠ -(k : ℂ)
  · rw [reciprocalGamma, dite_eq_left hp]
    have he := GammaOn_add_nat_div ⟨z,hp⟩ n
    rw [← he]
    have h0 : Gamma z ≠ 0 := GammaOn_ne_zero ⟨z,hp⟩
    have hn : Gamma (z+n) ≠ 0 := GammaOn_ne_zero (GammaPoint.ofRePos (z+n) hz)
    change (Gamma z)⁻¹ = (Gamma (z+n)/Gamma z)/Gamma (z+n)
    field_simp
  · rw [reciprocalGamma, dite_eq_right hp]
    push Not at hp
    obtain ⟨k,hk⟩ := hp
    have hkn : k < n := by
      rw [hk] at hz
      simp only [add_re,neg_re,natCast_re] at hz
      exact_mod_cast (show (k : ℝ) < n by linarith)
    have hP : (ascPochhammer ℂ n).eval z = 0 :=
      (ascPochhammer_eval_eq_zero_iff n z).mpr ⟨k,hkn,by rw [hk,neg_neg]⟩
    rw [hP,zero_div]

/-- Reciprocal Gamma is complex differentiable everywhere, including its zeros. -/
theorem differentiable_reciprocalGamma : Differentiable ℂ reciprocalGamma := by
  intro z
  obtain ⟨n,hn⟩ := exists_nat_gt (-z.re)
  have hz : 0 < (z+(n:ℂ)).re := by simp only [add_re,natCast_re]; linarith
  have hG := differentiableAt_Gamma (z+n) (GammaPoint.ofRePos (z+n) hz).property
  have hGn : Gamma (z+n) ≠ 0 := GammaOn_ne_zero (GammaPoint.ofRePos (z+n) hz)
  have hd : DifferentiableAt ℂ (fun w : ℂ ↦ (ascPochhammer ℂ n).eval w / Gamma (w+n)) z :=
    ((ascPochhammer ℂ n).hasDerivAt z).differentiableAt.div
      (hG.comp z (differentiableAt_id.add_const (n : ℂ))) hGn
  apply hd.congr_of_eventuallyEq
  have hnear : ∀ᶠ w in 𝓝 z, 0 < (w+(n:ℂ)).re :=
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun w : ℂ ↦ (w+(n:ℂ)).re))).mem_nhds hz
  filter_upwards [hnear] with w hw
  exact shifted_reciprocal n w hw

end Complex
