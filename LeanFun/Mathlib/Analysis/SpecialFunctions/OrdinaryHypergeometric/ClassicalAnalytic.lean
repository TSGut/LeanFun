/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric.Domain
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import LeanFun.Mathlib.Analysis.Analytic.OpenDomain
public import LeanFun.Mathlib.Analysis.Calculus.Deriv.OpenDomain
import Mathlib.Tactic.LinearCombination
/-! # Classical Gauss-series calculus on the unit disk
The argument type enforces the disk. Derivatives are actual derivatives on
that domain, with constant and linear cases separated before shifted values
are formed. References: DLMF15.2.1,15.5.1,15.10.1.
-/
@[expose] public noncomputable section
open Polynomial Filter
open scoped Topology
section ClassicalDisk
variable {K : Type*} [RCLike K]
open Set

private theorem gauss_cases (p : GaussParameters K) :
    (∀ n : ℕ, p.c ≠ -(n : K)) ∨ ∃ k : ℕ, p.a = -(k : K) ∨ p.b = -(k : K) := by
  classical
  by_cases hc : ∀ n : ℕ, p.c ≠ -(n : K)
  · exact Or.inl hc
  · push Not at hc
    obtain ⟨m, hm⟩ := hc
    have hz : (ascPochhammer K (m + 1)).eval p.c = 0 :=
      (ascPochhammer_eval_eq_zero_iff _ _).mpr ⟨m, Nat.lt_succ_self m, by rw [hm, neg_neg]⟩
    rcases mul_eq_zero.mp (p.denominator (m + 1) hz) with ha | hb
    · obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp ha
      exact Or.inr ⟨k, Or.inl (by simpa using congrArg Neg.neg hk.symm)⟩
    · obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp hb
      exact Or.inr ⟨k, Or.inr (by simpa using congrArg Neg.neg hk.symm)⟩

private theorem coefficient_imported_of_nonpole (p : GaussParameters K)
    (hc : ∀ n : ℕ, p.c ≠ -(n : K)) (n : ℕ) :
    ordinaryHypergeometricCoefficientOn p n = ordinaryHypergeometricCoefficient p.a p.b p.c n := by
  have hcn : (ascPochhammer K n).eval p.c ≠ 0 := by
    intro hz
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp hz
    exact hc k (by simpa using congrArg Neg.neg hk.symm)
  rw [ordinaryHypergeometricCoefficientOn_eq_div p n hcn]
  unfold ordinaryHypergeometricCoefficient
  ring

private theorem nonpole_radius (a b c : K) (hc : ∀ n : ℕ, c ≠ -(n : K)) :
    1 ≤ (ordinaryHypergeometricSeries K a b c).radius := by
  by_cases ha : ∃ k : ℕ, a = -(k : K)
  · obtain ⟨k, rfl⟩ := ha
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₁]
    exact le_top
  by_cases hb : ∃ k : ℕ, b = -(k : K)
  · obtain ⟨k, rfl⟩ := hb
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₂]
    exact le_top
  rw [ordinaryHypergeometricSeries_radius_eq_one]
  intro k
  exact ⟨fun h ↦ ha ⟨k, by simpa using (congrArg Neg.neg h).symm⟩,
    fun h ↦ hb ⟨k, by simpa using (congrArg Neg.neg h).symm⟩,
    fun h ↦ hc k (by simpa using (congrArg Neg.neg h).symm)⟩

private theorem nonpole_hasSum (a b c : K) (hc : ∀ n : ℕ, c ≠ -(n : K))
    {z : K} (hz : ‖z‖ < 1) :
    HasSum (fun n ↦ ordinaryHypergeometricCoefficient a b c n * z^n)
      (ordinaryHypergeometric a b c z) := by
  have hr := nonpole_radius a b c hc
  have hf : HasFPowerSeriesOnBall (ordinaryHypergeometric a b c)
      (ordinaryHypergeometricSeries K a b c) 0 1 :=
    ((ordinaryHypergeometricSeries K a b c).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le hr)).mono zero_lt_one hr
  have hs := hf.hasSum (y := z) (by
    rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
    exact_mod_cast hz)
  simpa only [ordinaryHypergeometricSeries_apply_eq, smul_eq_mul, zero_add] using hs



/-- Every point of the open unit disk is a classical Gauss-series point. -/
def GaussSeriesPoint.ofUnitDisk (p : GaussParameters K) (z : Metric.ball (0 : K) 1) :
    GaussSeriesPoint p := ⟨z.val, by
  classical
  rcases gauss_cases p with hc | ⟨k, hk⟩
  · have hs : HasSum (fun n ↦ ordinaryHypergeometricCoefficientOn p n * z.val ^ n)
        (ordinaryHypergeometric p.a p.b p.c z.val) := by
      simpa only [coefficient_imported_of_nonpole p hc] using
        nonpole_hasSum p.a p.b p.c hc
          (by simpa only [Metric.mem_ball, dist_zero_right] using z.property)
    exact ⟨_, hs.tendsto_sum_nat⟩
  · exact (GaussSeriesPoint.ofTerminating p k hk z.val).property⟩


/-- The genuine classical Gauss series converges throughout the open disk. -/
theorem hasSum_ordinaryHypergeometricOn (p : GaussParameters K)
    (z : Metric.ball (0 : K) 1) :
    HasSum (fun n ↦ ordinaryHypergeometricCoefficientOn p n * z.val ^ n)
      (ordinaryHypergeometricOn p (.ofUnitDisk p z)) := by
  rcases gauss_cases p with hc | ⟨k,hk⟩
  · have hs : HasSum (fun n ↦ ordinaryHypergeometricCoefficientOn p n * z.val ^ n)
        (ordinaryHypergeometric p.a p.b p.c z.val) := by
      simpa only [coefficient_imported_of_nonpole p hc] using
        nonpole_hasSum p.a p.b p.c hc
          (by simpa only [Metric.mem_ball, dist_zero_right] using z.property)
    rw [ordinaryHypergeometricOn_eq_of_tendsto p (.ofUnitDisk p z) hs.tendsto_sum_nat]
    exact hs
  · have hs : HasSum (fun n ↦ ordinaryHypergeometricCoefficientOn p n * z.val^n)
        (∑ n ∈ Finset.range (k+1), ordinaryHypergeometricCoefficientOn p n * z.val^n) :=
      hasSum_sum_of_ne_finset_zero (s := Finset.range (k+1))
        (f := fun n ↦ ordinaryHypergeometricCoefficientOn p n * z.val^n) (fun n hn ↦ by
          rw [ordinaryHypergeometricCoefficientOn_eq_zero_of_termination p hk
            (by simpa using hn), zero_mul])
    rw [ordinaryHypergeometricOn_eq_of_tendsto p (.ofUnitDisk p z) hs.tendsto_sum_nat]
    exact hs

/-- The classical coefficient series has radius at least one. -/
theorem one_le_ordinaryHypergeometricOn_radius (p : GaussParameters K) :
    1 ≤ (FormalMultilinearSeries.ofScalars K (ordinaryHypergeometricCoefficientOn p)).radius := by
  rcases gauss_cases p with hc | ⟨k, hk⟩
  · have he : ordinaryHypergeometricCoefficientOn p = ordinaryHypergeometricCoefficient p.a p.b p.c :=
      funext (coefficient_imported_of_nonpole p hc)
    simpa only [ordinaryHypergeometricSeries, he] using nonpole_radius p.a p.b p.c hc
  · have hz : ∀ᶠ n in atTop,
        (FormalMultilinearSeries.ofScalars K (ordinaryHypergeometricCoefficientOn p)) n = 0 := by
      filter_upwards [eventually_gt_atTop k] with n hn
      exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero K
        (ordinaryHypergeometricCoefficientOn_eq_zero_of_termination p hk hn)
    rw [FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero _ hz]
    exact le_top

/-- A genuine power-series representation on the disk, independent of extension values. -/
theorem hasFPowerSeriesOnBall_ordinaryHypergeometricOn (p : GaussParameters K) :
    ∃ g : K → K,
      (∀ z : Metric.ball (0 : K) 1,
        g z.val = ordinaryHypergeometricOn p (.ofUnitDisk p z)) ∧
      HasFPowerSeriesOnBall g
        (FormalMultilinearSeries.ofScalars K (ordinaryHypergeometricCoefficientOn p)) 0 1 := by
  classical
  let g : K → K := fun z ↦ if h : z ∈ Metric.ball (0 : K) 1 then
    ordinaryHypergeometricOn p (.ofUnitDisk p ⟨z,h⟩) else 0
  refine ⟨g, ?_, ?_⟩
  · intro z
    simp only [g, dite_eq_left z.property]
  · refine ⟨one_le_ordinaryHypergeometricOn_radius p, zero_lt_one, ?_⟩
    intro z hz
    have hz' : z ∈ Metric.ball (0 : K) 1 := by
      rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm] at hz
      rw [Metric.mem_ball, dist_zero_right]
      exact_mod_cast hz
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
      g, dite_eq_left hz', mul_comm] using hasSum_ordinaryHypergeometricOn p ⟨z,hz'⟩

/-- Analyticity is stated for the function with its domain in the argument type. -/
theorem analyticOnOpen_ordinaryHypergeometricOn (p : GaussParameters K) :
    AnalyticOnOpen ⟨Metric.ball (0 : K) 1, isOpen_ball⟩
      (fun z ↦ ordinaryHypergeometricOn p (.ofUnitDisk p z)) := by
  obtain ⟨g,hg,hf⟩ := hasFPowerSeriesOnBall_ordinaryHypergeometricOn p
  intro z
  refine ⟨g,hg,hf.analyticAt_of_mem ?_⟩
  rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
  have hz : ‖z.val‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using (show z.val ∈ Metric.ball (0 : K) 1 from z.property)
  exact_mod_cast hz

/-- Nonconstant Gauss data have the classical shifted first derivative. -/
theorem hasDerivAtOnOpen_ordinaryHypergeometricOn (p : GaussParameters K)
    (h : p.a * p.b ≠ 0) (z : Metric.ball (0 : K) 1) :
    HasDerivAtOnOpen ⟨Metric.ball (0 : K) 1, isOpen_ball⟩
      (fun y ↦ ordinaryHypergeometricOn p (.ofUnitDisk p y))
      (p.a * p.b / p.c * ordinaryHypergeometricOn (p.shift h) (.ofUnitDisk (p.shift h) z)) z := by
  obtain ⟨g,hg,hf⟩ := hasFPowerSeriesOnBall_ordinaryHypergeometricOn p
  refine ⟨g,hg,?_⟩
  have hmem : z.val ∈ Metric.eball (0 : K) 1 := by
    rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
    have hz : ‖z.val‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using z.property
    exact_mod_cast hz
  let s := FormalMultilinearSeries.ofScalars K (ordinaryHypergeometricCoefficientOn p)
  have hs := (ContinuousLinearMap.apply K K (1 : K)).hasSum (hf.fderiv.hasSum hmem)
  have he (n : ℕ) : s.derivSeries n (fun _ ↦ z.val) 1 =
      (p.a*p.b/p.c) * (ordinaryHypergeometricCoefficientOn (p.shift h) n * z.val^n) := by
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp only [_root_.smul_apply, FormalMultilinearSeries.derivSeries_coeff_one,
      s, FormalMultilinearSeries.coeff_ofScalars, nsmul_eq_mul, smul_eq_mul]
    rw [Nat.cast_add, Nat.cast_one, ordinaryHypergeometricCoefficientOn_shift p h]
    ring
  change HasSum (fun n ↦ s.derivSeries n (fun _ ↦ z.val) 1)
    (fderiv K g (0+z.val) 1) at hs
  simp_rw [he] at hs
  have hd := (hf.analyticAt_of_mem hmem).differentiableAt.hasDerivAt
  have heq := hs.unique ((hasSum_ordinaryHypergeometricOn (p.shift h) z).mul_left (p.a*p.b/p.c))
  exact hd.congr_deriv (by simpa only [deriv, zero_add] using heq)

/-- The constant case has derivative zero without assigning a shifted value. -/
theorem hasDerivAtOnOpen_ordinaryHypergeometricOn_constant (p : GaussParameters K)
    (h : p.a * p.b = 0) (z : Metric.ball (0 : K) 1) :
    HasDerivAtOnOpen ⟨Metric.ball (0 : K) 1, isOpen_ball⟩
      (fun y ↦ ordinaryHypergeometricOn p (.ofUnitDisk p y)) 0 z := by
  refine ⟨fun _ ↦ 1, ?_, hasDerivAt_const z.val 1⟩
  intro y
  symm
  have hs : HasSum (fun n ↦ ordinaryHypergeometricCoefficientOn p n * y.val^n)
      (∑ n ∈ ({0} : Finset ℕ), ordinaryHypergeometricCoefficientOn p n * y.val^n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn ↦ by
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simpa using hn)
      rw [ordinaryHypergeometricCoefficientOn_succ_of_constant p h, zero_mul])
  have h0 : ordinaryHypergeometricCoefficientOn p 0 = 1 := by
    simp [ordinaryHypergeometricCoefficientOn]
  simpa only [Finset.sum_singleton, h0, pow_zero, mul_one] using (hasSum_ordinaryHypergeometricOn p y).unique hs

end ClassicalDisk

section ClassicalCoefficientRecurrence
variable {K : Type*} [Field K] [CharZero K]
/-- The classical coefficient recurrence under its original non-pole hypothesis. -/
theorem ordinaryHypergeometricCoefficientOn_recurrence (p : GaussParameters K)
    (hc : ∀ k : ℕ, p.c + k ≠ 0) (n : ℕ) :
    ((n : K) + 1) * (p.c + n) * ordinaryHypergeometricCoefficientOn p (n + 1) =
      (p.a + n) * (p.b + n) * ordinaryHypergeometricCoefficientOn p n := by
  have hd (m : ℕ) : (ascPochhammer K m).eval p.c ≠ 0 := by
    intro hz
    obtain ⟨k,_,hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp hz
    apply hc k
    rw [hk, add_neg_cancel]
  rw [ordinaryHypergeometricCoefficientOn_eq_div p (n+1) (hd _),
    ordinaryHypergeometricCoefficientOn_eq_div p n (hd _)]
  simp only [ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hn : (n : K)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [hd n, hc n]

/-- Normalized recurrence solutions equal the classical coefficients. -/
theorem eq_ordinaryHypergeometricCoefficientOn_of_recurrence (p : GaussParameters K)
    (hc : ∀ k : ℕ, p.c + k ≠ 0) {u : ℕ → K} (hzero : u 0 = 1)
    (hrec : ∀ n : ℕ, ((n : K) + 1) * (p.c + n) * u (n + 1) =
      (p.a + n) * (p.b + n) * u n) :
    u = ordinaryHypergeometricCoefficientOn p := by
  funext n
  induction n with
  | zero => simpa [ordinaryHypergeometricCoefficientOn] using hzero
  | succ n ih =>
    have hn : (n : K)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    apply mul_left_cancel₀ (mul_ne_zero hn (hc n))
    rw [hrec, ordinaryHypergeometricCoefficientOn_recurrence p hc, ih]

end ClassicalCoefficientRecurrence


section ClassicalSeriesAndODE
variable {K : Type*} [RCLike K]
open Set



private def nonpoleShift (p : GaussParameters K) (hc : ∀ n : ℕ, p.c+n ≠ 0) : GaussParameters K :=
  .ofNoPole (p.a+1) (p.b+1) (p.c+1) (by
    intro n hn
    apply hc (n+1)
    push_cast
    linear_combination hn)
private theorem nonpoleShift_domain (p : GaussParameters K) (hc : ∀ n : ℕ, p.c+n ≠ 0)
    (n : ℕ) : (nonpoleShift p hc).c+n ≠ 0 := by
  intro hn
  apply hc (n+1)
  dsimp [nonpoleShift, GaussParameters.ofNoPole] at hn
  push_cast
  linear_combination hn
private theorem shift_coeff (p : GaussParameters K) (hc : ∀ n : ℕ, p.c+n ≠ 0) (n : ℕ) :
    ((n : K)+1)*ordinaryHypergeometricCoefficientOn p (n+1) =
      (p.a*p.b/p.c)*ordinaryHypergeometricCoefficientOn (nonpoleShift p hc) n := by
  by_cases h : p.a*p.b = 0
  · rw [ordinaryHypergeometricCoefficientOn_succ_of_constant p h, h]
    simp
  · exact ordinaryHypergeometricCoefficientOn_shift p h n
private theorem shift_deriv (p : GaussParameters K) (hc : ∀ n : ℕ, p.c+n ≠ 0)
    (z : Metric.ball (0 : K) 1) :
    HasDerivAtOnOpen ⟨Metric.ball (0 : K) 1, Metric.isOpen_ball⟩
      (fun y ↦ ordinaryHypergeometricOn p (.ofUnitDisk p y))
      ((p.a*p.b/p.c)*ordinaryHypergeometricOn (nonpoleShift p hc)
        (.ofUnitDisk (nonpoleShift p hc) z)) z := by
  by_cases h : p.a*p.b = 0
  · simpa only [h, zero_div, zero_mul] using
      hasDerivAtOnOpen_ordinaryHypergeometricOn_constant p h z
  · exact hasDerivAtOnOpen_ordinaryHypergeometricOn p h z
private theorem hasSum_shift_mul_pow {u : ℕ → K} {z s : K}
    (h : HasSum (fun n : ℕ ↦ u (n+1)*z^n) s) :
    HasSum (fun n : ℕ ↦ u n*z^n) (s*z+u 0) := by
  have hh : HasSum (fun n : ℕ ↦ u (n+1)*z^(n+1)) (s*z) := by
    simpa only [pow_succ, mul_assoc] using h.mul_right z
  simpa using (hasSum_nat_add_iff (f := fun n : ℕ ↦ u n*z^n) 1).mp hh

private theorem gauss_ode_of_hasSum (a b c z f d e : K) (u : ℕ → K)
    (h0 : HasSum (fun n : ℕ ↦ u n*z^n) f)
    (h1 : HasSum (fun n : ℕ ↦ ((n : K)+1)*u (n+1)*z^n) d)
    (h2 : HasSum (fun n : ℕ ↦ ((n : K)+1)*((n : K)+2)*u (n+2)*z^n) e)
    (hr : ∀ n : ℕ, ((n : K)+1)*(c+n)*u (n+1) = (a+n)*(b+n)*u n) :
    z*(1-z)*e+(c-(a+b+1)*z)*d-a*b*f = 0 := by
  have hN : HasSum (fun n : ℕ ↦ (n : K)*u n*z^n) (d*z) := by
    have h := hasSum_shift_mul_pow (u := fun n : ℕ ↦ (n : K)*u n)
      (by simpa only [Nat.cast_add, Nat.cast_one] using h1)
    simpa using h
  have hNE : HasSum (fun n : ℕ ↦ (n : K)*((n : K)+1)*u (n+1)*z^n) (e*z) := by
    have h := hasSum_shift_mul_pow (u := fun n : ℕ ↦ (n : K)*((n : K)+1)*u (n+1))
      (s := e) (z := z) (by
        convert h2 using 1
        funext n
        push_cast
        congr 1; ring)
    simpa using h
  have hNN : HasSum (fun n : ℕ ↦ (n : K)*((n : K)-1)*u n*z^n) (e*z*z) := by
    have h := hasSum_shift_mul_pow (u := fun n : ℕ ↦ (n : K)*((n : K)-1)*u n)
      (s := e*z) (z := z) (by
        convert hNE using 1
        funext n
        push_cast
        ring)
    simpa using h
  have hL := (h1.mul_left c).add hNE
  have hR := ((h0.mul_left (a*b)).add (hN.mul_left (a+b+1))).add hNN
  have he : (fun n : ℕ ↦ c*(((n : K)+1)*u (n+1)*z^n) +
        (n : K)*((n : K)+1)*u (n+1)*z^n) =
      (fun n : ℕ ↦ a*b*(u n*z^n)+(a+b+1)*((n : K)*u n*z^n)+
        (n : K)*((n : K)-1)*u n*z^n) := by
    funext n
    linear_combination z^n * hr n
  rw [he] at hL
  have hh := hL.unique hR
  linear_combination hh

/-- The differential equation asserts genuine first and second derivatives on the disk. -/
theorem ordinaryHypergeometricOn_ode (p : GaussParameters K)
    (hc : ∀ n : ℕ, p.c + n ≠ 0) :
    ∃ d₁ d₂ : Metric.ball (0 : K) 1 → K,
      ∀ z : Metric.ball (0 : K) 1,
        HasDerivAtOnOpen ⟨Metric.ball (0 : K) 1, isOpen_ball⟩
          (fun y ↦ ordinaryHypergeometricOn p (.ofUnitDisk p y)) (d₁ z) z ∧
        HasDerivAtOnOpen ⟨Metric.ball (0 : K) 1, isOpen_ball⟩ d₁ (d₂ z) z ∧
        z.val * (1 - z.val) * d₂ z +
          (p.c - (p.a + p.b + 1) * z.val) * d₁ z -
            p.a * p.b * ordinaryHypergeometricOn p (.ofUnitDisk p z) = 0 := by
  let q := nonpoleShift p hc
  have hq := nonpoleShift_domain p hc
  let r := nonpoleShift q hq
  refine ⟨fun z ↦ (p.a*p.b/p.c)*ordinaryHypergeometricOn q (.ofUnitDisk q z),
    fun z ↦ (p.a*p.b/p.c)*(q.a*q.b/q.c)*ordinaryHypergeometricOn r (.ofUnitDisk r z), ?_⟩
  intro z
  refine ⟨shift_deriv p hc z, ?_, ?_⟩
  · convert (shift_deriv q hq z).const_mul (p.a*p.b/p.c) using 1
    simp only [r, mul_assoc]
  · apply gauss_ode_of_hasSum p.a p.b p.c z.val _ _ _ (ordinaryHypergeometricCoefficientOn p)
      (hasSum_ordinaryHypergeometricOn p z)
    · convert (hasSum_ordinaryHypergeometricOn q z).mul_left (p.a*p.b/p.c) using 1
      ext n
      rw [shift_coeff p hc]
      ring
    · convert (hasSum_ordinaryHypergeometricOn r z).mul_left
        ((p.a*p.b/p.c)*(q.a*q.b/q.c)) using 1
      ext n
      rw [show (n : K)+2 = ((n+1 : ℕ) : K)+1 by push_cast; ring,
        mul_assoc ((n : K)+1), shift_coeff p hc (n+1)]
      have hh := shift_coeff q hq n
      linear_combination (p.a*p.b/p.c)*z.val^n*hh
    · exact ordinaryHypergeometricCoefficientOn_recurrence p hc

end ClassicalSeriesAndODE

section ClassicalSecondDerivative
variable {K : Type*} [RCLike K]
open Set

/-- Second derivatives use shifted values only when both numerator factors are nonzero. -/
theorem hasIteratedDerivOnOpen_ordinaryHypergeometricOn_two (p : GaussParameters K)
    (h₁ : p.a * p.b ≠ 0) (h₂ : (p.a + 1) * (p.b + 1) ≠ 0) :
    HasIteratedDerivOnOpen ⟨Metric.ball (0 : K) 1, isOpen_ball⟩ 2
      (fun z ↦ ordinaryHypergeometricOn p (.ofUnitDisk p z))
      (fun z ↦ (p.a * p.b / p.c) * ((p.a + 1) * (p.b + 1) / (p.c + 1)) *
        ordinaryHypergeometricOn ((p.shift h₁).shift h₂)
          (.ofUnitDisk ((p.shift h₁).shift h₂) z)) := by
  refine ⟨fun z ↦ (p.a * p.b / p.c) *
    ordinaryHypergeometricOn (p.shift h₁) (.ofUnitDisk (p.shift h₁) z), ?_, ?_⟩
  · exact ⟨_, rfl, fun z ↦ hasDerivAtOnOpen_ordinaryHypergeometricOn p h₁ z⟩
  · intro z
    simpa only [GaussParameters.shift, mul_assoc] using
      (hasDerivAtOnOpen_ordinaryHypergeometricOn (p.shift h₁) h₂ z).const_mul
        (p.a * p.b / p.c)

/-- A constant Gauss series has a genuine zero second derivative. -/
theorem hasIteratedDerivOnOpen_ordinaryHypergeometricOn_two_constant (p : GaussParameters K)
    (h : p.a * p.b = 0) :
    HasIteratedDerivOnOpen ⟨Metric.ball (0 : K) 1, isOpen_ball⟩ 2
      (fun z ↦ ordinaryHypergeometricOn p (.ofUnitDisk p z)) (fun _ ↦ 0) := by
  refine ⟨fun _ ↦ 0, ⟨_, rfl, fun z ↦ hasDerivAtOnOpen_ordinaryHypergeometricOn_constant p h z⟩,
    fun z ↦ ⟨fun _ ↦ 0, fun _ ↦ rfl, hasDerivAt_const z.val (0 : K)⟩⟩

/-- Linear terminating cases have zero second derivative without a twice-shifted value. -/
theorem hasIteratedDerivOnOpen_ordinaryHypergeometricOn_two_linear (p : GaussParameters K)
    (h₁ : p.a * p.b ≠ 0) (h₂ : (p.a + 1) * (p.b + 1) = 0) :
    HasIteratedDerivOnOpen ⟨Metric.ball (0 : K) 1, isOpen_ball⟩ 2
      (fun z ↦ ordinaryHypergeometricOn p (.ofUnitDisk p z)) (fun _ ↦ 0) := by
  refine ⟨fun z ↦ (p.a * p.b / p.c) *
    ordinaryHypergeometricOn (p.shift h₁) (.ofUnitDisk (p.shift h₁) z), ?_, ?_⟩
  · exact ⟨_, rfl, fun z ↦ hasDerivAtOnOpen_ordinaryHypergeometricOn p h₁ z⟩
  · intro z
    simpa only [mul_zero] using
      (hasDerivAtOnOpen_ordinaryHypergeometricOn_constant (p.shift h₁) h₂ z).const_mul
        (p.a * p.b / p.c)
end ClassicalSecondDerivative

