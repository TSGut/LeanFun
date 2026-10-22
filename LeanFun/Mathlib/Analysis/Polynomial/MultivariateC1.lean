/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.Calculus.FDeriv.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.CommRing
public import LeanFun.Mathlib.Algebra.MvPolynomial.PolynomialDerivative
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraApproximation
/-! # Simultaneous approximation of values and first derivatives on a square

A smooth real function on the plane admits polynomial approximants controlling
its values and both Cartesian first derivatives on the unit square. Approximate
the mixed derivative and the two axis traces by polynomials, then integrate
polynomials and fix the value at the origin. The mean value theorem gives the
simultaneous error bound. This supplies the C¹ approximation step in polynomial
Sobolev density; see Evans, *Partial Differential Equations*, Chapter 5.
-/

@[expose] public noncomputable section
namespace MvPolynomial
variable {σ : Type*}
private theorem exists_pderiv_eq_vanishing (i : σ) (p : MvPolynomial σ ℝ) :
    ∃ q : MvPolynomial σ ℝ, pderiv i q = p ∧ ∀ x : σ → ℝ, x i = 0 → eval x q = 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P, hP, hPv⟩ := hp
    obtain ⟨Q, hQ, hQv⟩ := hq
    exact ⟨P+Q, by simp [hP,hQ], fun x hx ↦ by simp [hPv x hx,hQv x hx]⟩
  | monomial d c =>
    refine ⟨monomial (d+Finsupp.single i 1) (c / ((d i : ℝ)+1)), ?_, ?_⟩
    · simp only [pderiv_monomial, add_tsub_cancel_right, Finsupp.add_apply,
        Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
      rw [div_mul_cancel₀ _ (by positivity)]
    · intro x hx
      rw [monomial_add_single, eval_mul, eval_pow, eval_X, hx]
      simp

private theorem pderiv_commute (i j : σ) (p : MvPolynomial σ ℝ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p k hp =>
    simp only [pderiv_mul, map_add, pderiv_X, Pi.single_apply, hp]
    split_ifs <;> simp
    ring
end MvPolynomial

namespace Polynomial
private theorem exists_derivative_eq_vanishing (p : Polynomial ℝ) :
    ∃ q : Polynomial ℝ, q.derivative = p ∧ q.eval 0 = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P,hP,hP0⟩ := hp
    obtain ⟨Q,hQ,hQ0⟩ := hq
    exact ⟨P+Q,by simp [hP,hQ],by simp [hP0,hQ0]⟩
  | monomial n c =>
    refine ⟨monomial (n+1) (c/((n:ℝ)+1)),?_,?_⟩
    · simp only [derivative_monomial, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [div_mul_cancel₀ _ (by positivity)]
    · simp
end Polynomial
namespace MvPolynomial
local notation "E" => (Fin 2 → ℝ)
private theorem eval_univariate (p : Polynomial ℝ) (i : Fin 2) (x : E) :
    eval x (p.eval₂ C (X i)) = p.eval (x i) := by
  rw [Polynomial.hom_eval₂]
  have h : (eval x).comp C = RingHom.id ℝ := by ext; simp
  rw [h,eval_X,Polynomial.eval₂_id]

private theorem exists_rectangle_polynomial (P : MvPolynomial (Fin 2) ℝ)
    (a b : Polynomial ℝ) (c : ℝ) :
    ∃ p : MvPolynomial (Fin 2) ℝ,
      pderiv 0 (pderiv 1 p) = P ∧
      (∀ t : ℝ, eval ![t,0] (pderiv 0 p) = a.eval t) ∧
      (∀ t : ℝ, eval ![0,t] (pderiv 1 p) = b.eval t) ∧ eval (0 : E) p = c := by
  obtain ⟨A,hA,hA0⟩ := exists_pderiv_eq_vanishing 0 P
  obtain ⟨Q,hQ,hQ0⟩ := exists_pderiv_eq_vanishing 1 A
  obtain ⟨U,hU,hU0⟩ := a.exists_derivative_eq_vanishing
  obtain ⟨V,hV,hV0⟩ := b.exists_derivative_eq_vanishing
  have hQd (t : ℝ) : eval ![t,0] (pderiv 0 Q) = 0 := by
    have hd := ((Q.contDiff_eval.differentiable (by simp)).differentiableAt
      (x := Function.update (![t,0] : E) 0 t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update (![t,0] : E) 0 t)
    have hu : Function.update (![t,0] : E) 0 t = ![t,0] := by ext i; fin_cases i <;> simp
    have hd' : HasDerivAt (fun r : ℝ ↦ eval (Function.update (![t,0] : E) 0 r) Q)
        (eval ![t,0] (pderiv 0 Q)) t := by
      simpa only [Function.comp_def,hu,fderiv_eval_single] using hd
    have hz : (fun r : ℝ ↦ eval (Function.update (![t,0] : E) 0 r) Q) = fun _ ↦ (0 : ℝ) := by
      funext r
      apply hQ0
      simp
    rw [hz] at hd'
    simpa using hd'.deriv.symm
  refine ⟨Q + U.eval₂ C (X 0) + V.eval₂ C (X 1) + C c, ?_, ?_, ?_, ?_⟩
  · simp [pderiv_polynomial_eval₂_C,hQ,hA]
  · intro t
    simp [pderiv_polynomial_eval₂_C,hU,eval_univariate,hQd]
  · intro t
    simp [pderiv_polynomial_eval₂_C,hQ,hV,eval_univariate,hA0 (![0,t]) (by simp)]
  · simp only [eval_add,eval_C,eval_univariate,Pi.zero_apply,hQ0 0 rfl,hU0,hV0,zero_add]
end MvPolynomial
open Set Filter
open scoped Topology ContDiff
namespace CartesianApproximation
private abbrev E := Fin 2 → ℝ
private def box : Set E := Icc (fun _ ↦ -1) (fun _ ↦ 1)
private theorem smooth_D {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 2) :
    ContDiff ℝ ∞ ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem hasDerivAt_slice {f : E → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 2) (x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ f (Function.update x i t)) ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i f (Function.update x i t)) t :=
  (hf _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)

private theorem D_comm {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 2) (x : E) :
    (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) j f) x = (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) j ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i f) x := by
  have hd := (hf.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  dsimp only
  simp only [fderiv_clm_apply (hd x) (differentiableAt_const _),
    fderiv_const_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

private theorem update_mem_box {x : E} (hx : x ∈ box) (i : Fin 2) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : Function.update x i t ∈ box := by
  constructor <;> intro j <;> by_cases h : j = i
  · subst j; simpa using ht.1
  · simpa [Function.update_of_ne h] using hx.1 j
  · subst j; simpa using ht.2
  · simpa [Function.update_of_ne h] using hx.2 j

private theorem slice_bound {f : E → ℝ} (hf : Differentiable ℝ f) (i : Fin 2) {C : ℝ}
    (hb : ∀ x ∈ box, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i f x| ≤ C) {x : E} (hx : x ∈ box)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    |f (Function.update x i t) - f x| ≤ C * |t-x i| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ Icc (-1 : ℝ) 1) ↦ (hasDerivAt_slice hf i x t).differentiableAt)
    (fun t ht ↦ by rw [(hasDerivAt_slice hf i x t).deriv]; exact hb _ (update_mem_box hx i ht))
    (convex_Icc (-1 : ℝ) 1) ⟨hx.1 i,hx.2 i⟩ ht
  simpa using h

private theorem D_sub {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 2) : (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i (fun x ↦ f x-g x) = fun x ↦ (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i f x-(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i g x := by
  funext x
  simp only [fderiv_fun_sub (hf x) (hg x),sub_apply]

private theorem D_eval (p : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
    (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i (fun x ↦ MvPolynomial.eval x p) = fun x ↦ MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
  funext x
  exact MvPolynomial.fderiv_eval_single p i x

private theorem rectangle_C1_bound {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {δ : ℝ} (hδ : 0 ≤ δ)
    (h0 : f 0 = 0)
    (hxy : ∀ x ∈ box, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 f) x| ≤ δ)
    (hx0 : ∀ t ∈ Icc (-1 : ℝ) 1, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 f ![t,0]| ≤ δ)
    (hy0 : ∀ t ∈ Icc (-1 : ℝ) 1, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 f ![0,t]| ≤ δ)
    {x : E} (hx : x ∈ box) : |f x| ≤ 4*δ ∧ ∀ i, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i f x| ≤ 2*δ := by
  have hz : (0 : E) ∈ box := by constructor <;> intro i <;> norm_num
  have habs (i : Fin 2) : |x i| ≤ 1 := abs_le.mpr ⟨hx.1 i,hx.2 i⟩
  have hd : ∀ x ∈ box, ∀ i : Fin 2, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i f x| ≤ 2*δ := by
    intro z hz' i
    have habs' (j : Fin 2) : |z j| ≤ 1 := abs_le.mpr ⟨hz'.1 j,hz'.2 j⟩
    fin_cases i
    · let y : E := ![z 0,0]
      have hy : y ∈ box := by constructor <;> intro j <;> fin_cases j <;> dsimp [y] <;> linarith [hz'.1 0,hz'.2 0]
      have hu : Function.update y 1 (z 1) = z := by ext j; fin_cases j <;> simp [y]
      have h := slice_bound ((smooth_D hf 0).differentiable (by simp)) 1 hxy hy ⟨hz'.1 1,hz'.2 1⟩
      simp only [hu,show y 1 = 0 from rfl,sub_zero] at h
      have h' := abs_sub_le ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 f z) ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 f y) 0
      simp only [sub_zero] at h'
      have hy' := hx0 (z 0) ⟨hz'.1 0,hz'.2 0⟩
      have hm := mul_le_mul_of_nonneg_left (habs' 1) hδ
      dsimp [y] at h h'
      change |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 f z| ≤ 2*δ
      nlinarith
    · let y : E := ![0,z 1]
      have hy : y ∈ box := by constructor <;> intro j <;> fin_cases j <;> dsimp [y] <;> linarith [hz'.1 1,hz'.2 1]
      have hu : Function.update y 0 (z 0) = z := by ext j; fin_cases j <;> simp [y]
      have hxy' : ∀ w ∈ box, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 f) w| ≤ δ := by
        intro w hw; rw [D_comm hf]; exact hxy w hw
      have h := slice_bound ((smooth_D hf 1).differentiable (by simp)) 0 hxy' hy ⟨hz'.1 0,hz'.2 0⟩
      simp only [hu,show y 0 = 0 from rfl,sub_zero] at h
      have h' := abs_sub_le ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 f z) ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 f y) 0
      simp only [sub_zero] at h'
      have hy' := hy0 (z 1) ⟨hz'.1 1,hz'.2 1⟩
      have hm := mul_le_mul_of_nonneg_left (habs' 0) hδ
      dsimp [y] at h h'
      change |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 f z| ≤ 2*δ
      nlinarith
  refine ⟨?_,hd x hx⟩
  let y : E := Function.update 0 0 (x 0)
  have hy : y ∈ box := update_mem_box hz 0 ⟨hx.1 0,hx.2 0⟩
  have hu : Function.update y 1 (x 1) = x := by ext i; fin_cases i <;> simp [y]
  have h1 := slice_bound (hf.differentiable (by simp)) 0 (fun z hz ↦ hd z hz 0) hz ⟨hx.1 0,hx.2 0⟩
  have h2 := slice_bound (hf.differentiable (by simp)) 1 (fun z hz ↦ hd z hz 1) hy ⟨hx.1 1,hx.2 1⟩
  simp only [hu,show y 1 = 0 from rfl,h0,Pi.zero_apply,sub_zero] at h1 h2
  have ht := abs_sub_le (f x) (f y) 0
  simp only [sub_zero] at ht
  have hm0 := mul_le_mul_of_nonneg_left (habs 0) (show 0 ≤ 2*δ by positivity)
  have hm1 := mul_le_mul_of_nonneg_left (habs 1) (show 0 ≤ 2*δ by positivity)
  change |f y| ≤ _ at h1
  nlinarith
end CartesianApproximation
namespace CartesianApproximation
private theorem exists_polynomial_C1_near {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 2) ℝ, ∀ x ∈ box,
      |MvPolynomial.eval x p-f x| < ε ∧
      ∀ i : Fin 2, |MvPolynomial.eval x (MvPolynomial.pderiv i p)-(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i f x| < ε := by
  let δ := ε/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨P,hP⟩ := MvPolynomial.exists_polynomial_near_on_compact
    (show IsCompact box from isCompact_Icc)
    ((smooth_D (smooth_D hf 0) 1).continuous.continuousOn) hδ
  have hxC : Continuous (fun t : ℝ ↦ (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 f ![t,0]) :=
    (smooth_D hf 0).continuous.comp (by fun_prop)
  have hyC : Continuous (fun t : ℝ ↦ (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 f ![0,t]) :=
    (smooth_D hf 1).continuous.comp (by fun_prop)
  obtain ⟨a,ha⟩ := exists_polynomial_near_of_continuousOn (-1) 1 _ hxC.continuousOn δ hδ
  obtain ⟨b,hb⟩ := exists_polynomial_near_of_continuousOn (-1) 1 _ hyC.continuousOn δ hδ
  obtain ⟨p,hpxy,hpx,hpy,hp0⟩ := MvPolynomial.exists_rectangle_polynomial P a b (f 0)
  have hp : ContDiff ℝ ∞ (fun x : E ↦ MvPolynomial.eval x p) := p.contDiff_eval.of_le (by simp)
  let e : E → ℝ := fun x ↦ f x-MvPolynomial.eval x p
  have he : ContDiff ℝ ∞ e := hf.sub hp
  have he0 : e 0 = 0 := by change f 0 - MvPolynomial.eval 0 p = 0; rw [hp0,sub_self]
  have hed (i : Fin 2) : (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i e = fun x ↦ (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) i f x-MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
    simpa only [e, MvPolynomial.fderiv_eval_single] using D_sub (hf.differentiable (by simp)) (hp.differentiable (by simp)) i
  have hexy : (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 e) = fun x ↦ (fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 f) x-MvPolynomial.eval x P := by
    rw [hed 0,D_sub ((smooth_D hf 0).differentiable (by simp))
      ((MvPolynomial.pderiv 0 p).contDiff_eval.differentiable (by simp)),D_eval,
      MvPolynomial.pderiv_commute 1 0 p,hpxy]
  have hxy : ∀ x ∈ box, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 ((fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 e) x| ≤ δ := by
    intro x hx
    rw [hexy,abs_sub_comm]
    exact (hP x hx).le
  have hx0 : ∀ t ∈ Icc (-1 : ℝ) 1, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 0 e ![t,0]| ≤ δ := by
    intro t ht
    rw [hed 0]
    dsimp only
    rw [hpx,abs_sub_comm]
    exact (ha t ht).le
  have hy0 : ∀ t ∈ Icc (-1 : ℝ) 1, |(fun (i : Fin 2) (f : E → ℝ) (x : E) ↦ fderiv ℝ f x (Pi.single i 1)) 1 e ![0,t]| ≤ δ := by
    intro t ht
    rw [hed 1]
    dsimp only
    rw [hpy,abs_sub_comm]
    exact (hb t ht).le
  refine ⟨p,fun x hx ↦ ?_⟩
  obtain ⟨hv,hd⟩ := rectangle_C1_bound he hδ.le he0 hxy hx0 hy0 hx
  constructor
  · rw [abs_sub_comm]
    exact hv.trans_lt (by dsimp [δ]; linarith)
  · intro i
    rw [abs_sub_comm]
    have h := hd i
    rw [hed i] at h
    exact h.trans_lt (by dsimp [δ]; linarith)
end CartesianApproximation

namespace MvPolynomial
/-- Smooth functions admit polynomial approximation of values and Cartesian first
 derivatives on the square, as used in the standard Sobolev density argument. -/
theorem exists_polynomial_C1_near_on_square {f : (Fin 2 → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 2) ℝ,
      ∀ x ∈ Set.Icc (fun _ : Fin 2 ↦ (-1 : ℝ)) (fun _ ↦ 1),
        |eval x p-f x| < ε ∧ ∀ i : Fin 2,
          |eval x (pderiv i p)-fderiv ℝ f x (Pi.single i 1)| < ε :=
  CartesianApproximation.exists_polynomial_C1_near hf hε
end MvPolynomial
