/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.GegenbauerIntegrability
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import LeanFun.Mathlib.Analysis.Calculus.Deriv.OpenDomain
public import LeanFun.Mathlib.Analysis.SpecialFunctions.PowerLaw.ClassicalWeighted

/-! # Moving the power-law singularity to the origin

The interval Möbius substitution fixes the integration domain and moves the
kernel singularity to zero. This is a step toward the degree-zero hypergeometric
formula in Gutleb–Carrillo–Olver, arXiv:2011.00045, Section 2.
-/

@[expose] public noncomputable section
open MeasureTheory Set Polynomial
namespace Real


/-- Its denominator is positive throughout the open square. -/
private theorem powerLawMobius_den_pos {x t : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < 1-x*t := by
  have ha := abs_lt.mpr hx
  have hb := abs_lt.mpr ht
  have hp : |x| * |t| < 1 :=
    (mul_le_mul_of_nonneg_right ha.le (abs_nonneg t)).trans_lt (by simpa using hb)
  have hh := le_abs_self (x*t)
  rw [abs_mul] at hh
  linarith

/-- The substitution remains strictly inside the interval. -/
private theorem powerLawMobius_mem {x t : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (fun (x t : ℝ) ↦ (x-t)/(1-x*t)) x t ∈ Ioo (-1 : ℝ) 1 := by
  have hd := powerLawMobius_den_pos hx ht
  constructor
  · rw [ lt_div_iff₀ hd]
    nlinarith [mul_pos (by linarith [hx.1] : 0 < 1+x) (by linarith [ht.2] : 0 < 1-t)]
  · rw [ div_lt_iff₀ hd]
    nlinarith [mul_pos (by linarith [hx.2] : 0 < 1-x) (by linarith [ht.1] : 0 < 1+t)]

/-- The same substitution is its own inverse on the open interval. -/
private theorem powerLawMobius_involutive {x t : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (fun (x t : ℝ) ↦ (x-t)/(1-x*t)) x ((fun (x t : ℝ) ↦ (x-t)/(1-x*t)) x t) = t := by
  have hd := powerLawMobius_den_pos hx ht
  have hd' := powerLawMobius_den_pos hx (powerLawMobius_mem hx ht)
  dsimp only at hd' ⊢
  apply (div_eq_iff hd'.ne').mpr
  field_simp
  ring


/-- Derivative of the interval substitution. -/
private theorem hasDerivAt_powerLawMobius {x t : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt ((fun (x t : ℝ) ↦ (x-t)/(1-x*t)) x) ((x^2-1)/(1-x*t)^2) t := by
  have h := ((hasDerivAt_const t x).sub (hasDerivAt_id t)).div
    ((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul x))
    (powerLawMobius_den_pos hx ht).ne'
  convert h using 1
  · funext s
    rfl
  · dsimp
    ring


/-- Algebraic transformation of the weight's quadratic factor. -/
private theorem one_sub_powerLawMobius_sq {x t : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    1-((fun (x t : ℝ) ↦ (x-t)/(1-x*t)) x t)^2 = (1-x^2)*(1-t^2)/(1-x*t)^2 := by
  have hd := powerLawMobius_den_pos hx ht
  dsimp only
  field_simp
  ring

/-- Algebraic transformation of the distance to the singularity. -/
private theorem sub_powerLawMobius {x t : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    x-(fun (x t : ℝ) ↦ (x-t)/(1-x*t)) x t = t*(1-x^2)/(1-x*t) := by
  have hd := powerLawMobius_den_pos hx ht
  dsimp only
  field_simp
  ring



end Real
namespace Real
/-- The full classical rational domain; the pole has no assigned value. -/
abbrev PowerLawMobiusDomain (x : ℝ) := {t : ℝ // 1-x*t ≠ 0}
def powerLawMobius (x : ℝ) (t : PowerLawMobiusDomain x) : ℝ :=
  (x-t.val)/(1-x*t.val)
theorem powerLawMobius_apply (x : ℝ) (t : PowerLawMobiusDomain x) :
    powerLawMobius x t = (x-t.val)/(1-x*t.val) := rfl

def PowerLawMobiusDomain.ofInterval (x t : Ioo (-1 : ℝ) 1) : PowerLawMobiusDomain x.val :=
  ⟨t.val,by exact (powerLawMobius_den_pos x.property t.property).ne'⟩

theorem powerLawMobius_den_posOn (x t : Ioo (-1 : ℝ) 1) :
    0 < 1-x.val*t.val := powerLawMobius_den_pos x.property t.property

theorem powerLawMobius_memOn (x t : Ioo (-1 : ℝ) 1) :
    powerLawMobius x.val (.ofInterval x t) ∈ Ioo (-1 : ℝ) 1 :=
  powerLawMobius_mem x.property t.property

theorem powerLawMobius_involutiveOn (x t : Ioo (-1 : ℝ) 1) :
    powerLawMobius x.val (.ofInterval x
      ⟨powerLawMobius x.val (.ofInterval x t),powerLawMobius_memOn x t⟩) = t.val :=
  powerLawMobius_involutive x.property t.property

theorem powerLawMobius_rangeOn (x : Ioo (-1 : ℝ) 1) :
    Set.range (fun t : Ioo (-1 : ℝ) 1 ↦ powerLawMobius x.val (.ofInterval x t)) =
      Ioo (-1 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨t,rfl⟩
    exact powerLawMobius_memOn x t
  · intro hy
    exact ⟨⟨powerLawMobius x.val (.ofInterval x ⟨y,hy⟩),powerLawMobius_memOn x ⟨y,hy⟩⟩,
      powerLawMobius_involutiveOn x ⟨y,hy⟩⟩

/-- A safe proof-local Möbius extension. Reference: Gutleb–Carrillo–Olver, Section 2. -/
private theorem exists_powerLawMobius_extension (x : Ioo (-1 : ℝ) 1) :
    ∃ M D : ℝ → ℝ,
      (∀ t : Ioo (-1 : ℝ) 1, M t.val = powerLawMobius x.val (.ofInterval x t)) ∧
      (∀ t : Ioo (-1 : ℝ) 1, D t.val = (x.val^2-1)/(1-x.val*t.val)^2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt M (D t) t) ∧
      InjOn M (Ioo (-1 : ℝ) 1) ∧ M '' Ioo (-1 : ℝ) 1 = Ioo (-1 : ℝ) 1 := by
  let M : ℝ → ℝ := fun t ↦ if h : t ∈ Ioo (-1 : ℝ) 1 then
    powerLawMobius x.val (.ofInterval x ⟨t,h⟩) else 0
  let D : ℝ → ℝ := fun t ↦ if h : t ∈ Ioo (-1 : ℝ) 1 then
    (x.val^2-1)/(1-x.val*(⟨t,h⟩ : Ioo (-1 : ℝ) 1).val)^2 else 0
  have hM (t : Ioo (-1 : ℝ) 1) : M t.val = powerLawMobius x.val (.ofInterval x t) := by simp only [M,dite_eq_left t.property]
  have hD (t : Ioo (-1 : ℝ) 1) : D t.val = (x.val^2-1)/(1-x.val*t.val)^2 := by simp only [D,dite_eq_left t.property]
  refine ⟨M,D,hM,hD,?_,?_,?_⟩
  · intro t ht
    rw [hD ⟨t,ht⟩]
    apply (hasDerivAt_powerLawMobius x.property ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hM ⟨s,hs⟩
  · intro a ha b hb he
    rw [hM ⟨a,ha⟩,hM ⟨b,hb⟩] at he
    have hh := congrArg (fun s ↦ (x.val-s)/(1-x.val*s)) he
    simpa only [powerLawMobius,PowerLawMobiusDomain.ofInterval,
      powerLawMobius_involutive x.property ha,powerLawMobius_involutive x.property hb] using hh
  · apply Set.Subset.antisymm
    · rintro _ ⟨t,ht,rfl⟩
      rw [hM ⟨t,ht⟩]
      exact powerLawMobius_memOn x ⟨t,ht⟩
    · intro t ht
      let u : Ioo (-1 : ℝ) 1 := ⟨powerLawMobius x.val (.ofInterval x ⟨t,ht⟩),powerLawMobius_memOn x ⟨t,ht⟩⟩
      refine ⟨u.val,u.property,?_⟩
      rw [hM u]
      exact powerLawMobius_involutiveOn x ⟨t,ht⟩

theorem hasDerivAtOnOpen_powerLawMobius (x t : Ioo (-1 : ℝ) 1) :
    HasDerivAtOnOpen ⟨Ioo (-1 : ℝ) 1,isOpen_Ioo⟩
      (fun s ↦ powerLawMobius x.val (.ofInterval x s))
      ((x.val^2-1)/(1-x.val*t.val)^2) t := by
  obtain ⟨M,D,hM,hD,hd,_,_⟩ := exists_powerLawMobius_extension x
  refine ⟨M,hM,?_⟩
  rw [← hD t]
  exact hd t.val t.property

theorem one_sub_powerLawMobius_sqOn (x t : Ioo (-1 : ℝ) 1) :
    1-(powerLawMobius x.val (.ofInterval x t))^2 =
      (1-x.val^2)*(1-t.val^2)/(1-x.val*t.val)^2 :=
  one_sub_powerLawMobius_sq x.property t.property

theorem sub_powerLawMobiusOn (x t : Ioo (-1 : ℝ) 1) :
    x.val-powerLawMobius x.val (.ofInterval x t) =
      t.val*(1-x.val^2)/(1-x.val*t.val) :=
  sub_powerLawMobius x.property t.property
end Real
namespace Real
local notation "μI" => Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume


/-- Change of variables for certified integrable inputs, using the safe extension. -/
private theorem integrable_integral_powerLawMobius_pullback (x : Ioo (-1 : ℝ) 1)
    (f : IntegrableInput μI) :
    Integrable (fun t : Ioo (-1 : ℝ) 1 ↦ ((1-x.val^2)/(1-x.val*t.val)^2)*
      f.val ⟨powerLawMobius x.val (.ofInterval x t),powerLawMobius_memOn x t⟩) μI ∧
    (∫ y, f.val y ∂μI) = ∫ t : Ioo (-1 : ℝ) 1,
      ((1-x.val^2)/(1-x.val*t.val)^2)*
      f.val ⟨powerLawMobius x.val (.ofInterval x t),powerLawMobius_memOn x t⟩ ∂μI := by
  obtain ⟨M,D,hM,hD,hd,hinj,himage⟩ := exists_powerLawMobius_extension x
  let F : ℝ → ℝ := Function.extend Subtype.val f.val (fun _ ↦ 0)
  have he (y : Ioo (-1 : ℝ) 1) : F y.val = f.val y :=
    Subtype.val_injective.extend_apply _ _ y
  have hg : IntegrableOn F (Ioo (-1 : ℝ) 1) volume := by
    apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mpr
    change Integrable (fun y : Ioo (-1 : ℝ) 1 ↦ F y.val) μI
    simpa only [he] using f.property
  have hj := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun t ht ↦ (hd t ht).hasDerivWithinAt) hinj F
  rw [himage] at hj
  have hi := (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp (hj.mp hg)
  have hv (t : Ioo (-1 : ℝ) 1) : |D t.val| • F (M t.val) =
      ((1-x.val^2)/(1-x.val*t.val)^2)*
        f.val ⟨powerLawMobius x.val (.ofInterval x t),powerLawMobius_memOn x t⟩ := by
    rw [hD t,hM t,he ⟨powerLawMobius x.val (.ofInterval x t),powerLawMobius_memOn x t⟩]
    have hn : x.val^2-1 < 0 := by nlinarith [x.property.1,x.property.2]
    simp only [smul_eq_mul,abs_div,abs_of_neg hn,abs_sq]
    ring
  constructor
  · convert hi using 1
    funext t
    exact (hv t).symm
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun t ht ↦ (hd t ht).hasDerivWithinAt) hinj F
    rw [himage] at h
    rw [← integral_subtype_comap (μ := volume) measurableSet_Ioo F,
      ← integral_subtype_comap (μ := volume) measurableSet_Ioo
        (fun t : ℝ ↦ |D t| • F (M t))] at h
    simpa only [he,hv] using h

theorem integrable_powerLawMobius_pullback (x : Ioo (-1 : ℝ) 1)
    (f : IntegrableInput μI) :
    Integrable (fun t : Ioo (-1 : ℝ) 1 ↦ ((1-x.val^2)/(1-x.val*t.val)^2)*
      f.val ⟨powerLawMobius x.val (.ofInterval x t),powerLawMobius_memOn x t⟩) μI := by
  exact (integrable_integral_powerLawMobius_pullback x f).1

end Real
namespace Real
local notation "μI" => Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume

def powerLawMobiusPullback (x : Ioo (-1 : ℝ) 1) (f : IntegrableInput μI) : IntegrableInput μI :=
  ⟨fun t ↦ ((1-x.val^2)/(1-x.val*t.val)^2)*
    f.val ⟨powerLawMobius x.val (.ofInterval x t),powerLawMobius_memOn x t⟩,
    integrable_powerLawMobius_pullback x f⟩

theorem powerLawMobiusPullback_apply (x : Ioo (-1 : ℝ) 1) (f : IntegrableInput μI)
    (t : Ioo (-1 : ℝ) 1) :
    (powerLawMobiusPullback x f).val t = ((1-x.val^2)/(1-x.val*t.val)^2)*
      f.val ⟨powerLawMobius x.val (.ofInterval x t),powerLawMobius_memOn x t⟩ := rfl

theorem integral_comp_powerLawMobiusOn (x : Ioo (-1 : ℝ) 1) (f : IntegrableInput μI) :
    (∫ y, f.val y ∂μI) = ∫ t, (powerLawMobiusPullback x f).val t ∂μI := by
  exact (integrable_integral_powerLawMobius_pullback x f).2

end Real
namespace Real

theorem powerLawMobius_den_pos_closed (x : Ioo (-1 : ℝ) 1) (t : Icc (-1 : ℝ) 1) :
    0 < 1-x.val*t.val := by
  have ha : |x.val| < 1 := abs_lt.mpr x.property
  have hb : |t.val| ≤ 1 := abs_le.mpr t.property
  have h := mul_le_mul_of_nonneg_left hb (abs_nonneg x.val)
  have hh := le_abs_self (x.val*t.val)
  rw [abs_mul] at hh
  nlinarith

def PowerLawInput.mobiusWeight (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) : PowerLawInput α.val 0 := by
  refine ⟨fun t ↦ (Polynomial.gegenbauerWeight lam.val ⟨t.val,t.property.1⟩ : ℝ)/
    (1-x.val*t.val)^(α.val+2*lam.val+1), ?_⟩
  let F : C(Icc (-1 : ℝ) 1,ℝ) := ⟨fun t ↦ 1/(1-x.val*t.val)^(α.val+2*lam.val+1),by
    apply continuous_const.div
      ((continuous_const.sub (continuous_const.mul continuous_subtype_val)).rpow_const
        (fun t ↦ Or.inl (powerLawMobius_den_pos_closed x t).ne'))
    intro t
    exact (rpow_pos_of_pos (powerLawMobius_den_pos_closed x t) _).ne'⟩
  have hi := (PowerLawInput.gegenbauerContinuous α lam ⟨0,by constructor <;> norm_num⟩ F).property
  convert hi using 1
  funext t
  change |0-t.val|^α.val*((Polynomial.gegenbauerWeight lam.val _ : ℝ)/_) =
    |0-t.val|^α.val*((Polynomial.gegenbauerWeight lam.val _ : ℝ)*(1/_))
  ring

theorem PowerLawInput.mobiusWeight_apply (α : Ioi (-1 : ℝ)) (lam : Ioi (-(1/2) : ℝ))
    (x : Ioo (-1 : ℝ) 1) (t : PowerLawDomain 0) :
    (PowerLawInput.mobiusWeight α lam x).val t =
      (Polynomial.gegenbauerWeight lam.val ⟨t.val,t.property.1⟩ : ℝ)/
        (1-x.val*t.val)^(α.val+2*lam.val+1) := rfl
end Real
namespace Real
local notation "μI" => Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume

theorem powerLawMobius_gegenbauer_integrandOn (α lam : ℝ)
    (x : Ioo (-1 : ℝ) 1) (t : PowerLawDomain 0) :
    ((1-x.val^2)/(1-x.val*t.val)^2)*
      (|x.val-powerLawMobius x.val (.ofInterval x ⟨t.val,t.property.1⟩)|^α *
        (Polynomial.gegenbauerWeight lam
          ⟨powerLawMobius x.val (.ofInterval x ⟨t.val,t.property.1⟩),
            powerLawMobius_memOn x ⟨t.val,t.property.1⟩⟩ : ℝ)) =
      (1-x.val^2)^(α+lam+1/2)*
        (|t.val|^α*(Polynomial.gegenbauerWeight lam ⟨t.val,t.property.1⟩ : ℝ)/
          (1-x.val*t.val)^(α+2*lam+1)) := by
  simp only [Polynomial.gegenbauerWeight_apply,powerLawMobius,PowerLawMobiusDomain.ofInterval]
  have hx := x.property
  have ht := t.property.1
  have hA : 0 < 1-x.val^2 := by nlinarith [hx.1,hx.2]
  have hB : 0 < 1-t.val^2 := by nlinarith [ht.1,ht.2]
  have hD := powerLawMobius_den_pos hx ht
  rw [sub_powerLawMobius hx ht,one_sub_powerLawMobius_sq hx ht,
    abs_div,abs_mul,abs_of_pos hA,abs_of_pos hD,
    div_rpow (mul_nonneg (abs_nonneg t.val) hA.le) hD.le,
    mul_rpow (abs_nonneg t.val) hA.le,
    div_rpow (mul_nonneg hA.le hB.le) (sq_nonneg _),mul_rpow hA.le hB.le]
  rw [show α+lam+1/2 = 1+α+(lam-1/2) by ring,
    show α+2*lam+1 = 2+α+2*(lam-1/2) by ring,
    rpow_add hA,rpow_add hA,rpow_one,
    rpow_add hD,rpow_add hD,rpow_mul hD.le]
  norm_cast
  simp only [mul_inv_rev,div_eq_mul_inv]
  ring

theorem powerLawIntegral_gegenbauerWeight_mobiusOn (α : Ioi (-1 : ℝ))
    (lam : Ioi (-(1/2) : ℝ)) (x : Ioo (-1 : ℝ) 1) :
    powerLawIntegral (.gegenbauerWeight α lam x) =
      (1-x.val^2)^(α.val+lam.val+1/2)*powerLawIntegral (.mobiusWeight α lam x) := by
  obtain ⟨F,hF,hi,hI⟩ := PowerLawInput.exists_weightedIntervalRepresentative
    (PowerLawInput.gegenbauerWeight α lam x)
  obtain ⟨G,hG,hj,hJ⟩ := PowerLawInput.exists_weightedIntervalRepresentative
    (PowerLawInput.mobiusWeight α lam x)
  let f : IntegrableInput μI := ⟨fun y ↦ F y.val,
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp hi)⟩
  have hleft : powerLawIntegral (.gegenbauerWeight α lam x) = ∫ y, f.val y ∂μI := by
    rw [hI]
    change (∫ y in (-1 : ℝ)..1, F y) = ∫ y : Ioo (-1 : ℝ) 1, F y.val ∂μI
    rw [integral_subtype_comap (μ := volume) measurableSet_Ioo,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]
  have hright : (∫ y : Ioo (-1 : ℝ) 1, G y.val ∂μI) =
      powerLawIntegral (.mobiusWeight α lam x) := by
    rw [hJ,integral_subtype_comap (μ := volume) measurableSet_Ioo,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]
  rw [hleft,integral_comp_powerLawMobiusOn]
  calc
    _ = ∫ t : Ioo (-1 : ℝ) 1, (1-x.val^2)^(α.val+lam.val+1/2)*G t.val ∂μI := by
      apply integral_congr_ae
      have hn : ∀ᵐ t : Ioo (-1 : ℝ) 1 ∂μI, t.val ≠ 0 :=
        (ae_restrict_iff_subtype measurableSet_Ioo).mp (ae_restrict_of_ae (volume.ae_ne 0))
      filter_upwards [hn] with t ht
      have hm : powerLawMobius x.val (.ofInterval x t) ≠ x.val := by
        intro he
        have hs := sub_powerLawMobiusOn x t
        rw [he,sub_self] at hs
        have hA : 0 < 1-x.val^2 := by nlinarith [x.property.1,x.property.2]
        have hd := powerLawMobius_den_posOn x t
        exact (div_ne_zero (mul_ne_zero ht hA.ne') hd.ne') hs.symm
      rw [powerLawMobiusPullback_apply]
      change _ * F (powerLawMobius x.val (.ofInterval x t)) = _
      rw [hF ⟨_,powerLawMobius_memOn x t,hm⟩,hG ⟨t.val,t.property,ht⟩,
        PowerLawInput.gegenbauerWeight_apply,PowerLawInput.mobiusWeight_apply]
      have h := powerLawMobius_gegenbauer_integrandOn α.val lam.val x ⟨t.val,t.property,ht⟩
      simpa only [zero_sub,abs_neg,mul_div_assoc] using h
    _ = (1-x.val^2)^(α.val+lam.val+1/2)*(∫ t : Ioo (-1 : ℝ) 1, G t.val ∂μI) :=
      integral_const_mul _ _
    _ = _ := by rw [hright]

end Real
