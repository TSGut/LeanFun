/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraToeplitzLimit
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraApproximateSolve

/-! # Stable first-kind sections of nonpolynomial operator limits

The Toeplitz limit is coercive up to sign; the remaining operator is compact.
Reference: Gutleb's thesis, §2.7; Böttcher–Silbermann finite-section theory.
-/

@[expose] public noncomputable section
open Polynomial Set Filter ContinuousLinearMap
open scoped Topology InnerProductSpace
namespace MvPolynomial
local notation "H" => lp (fun _ : ℕ ↦ ℝ) 2

private theorem positive_limit_stable
    (K : (Fin 2 → ℝ) → ℝ) (p : ℕ → MvPolynomial (Fin 2) ℝ)
    {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n)
    (herr : ∀ n x, x ∈ Icc (0 : ℝ) 1 →
      |eval (fun _ ↦ x) (p n)-K (fun _ ↦ x)| ≤ e n)
    (hte : Tendsto e atTop (𝓝 0))
    (A : H →L[ℝ] H) (hA : Tendsto (fun n ↦ volterraPreconditionedL2 (p n)) atTop (𝓝 A))
    (hinj : Function.Injective A)
    {a : ℝ} (ha : 0 < a) (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, a ≤ K (fun _ ↦ x)) :
    IsUnit A ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      IsUnit (coerciveFiniteSection (lp.initialL2Projection N) A) ∧
      ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N) A)‖ ≤ C := by
  obtain ⟨T,hc,hT⟩ := exists_coercive_volterraToeplitz_limit K p he herr hte A hA ha hdiag
  have hunit : IsUnit T := isUnit_of_re_inner_le T (half_pos ha) hT
  have heq : T+(A-T)=A := by abel
  have hu : IsUnit A := by
    rw [← heq]
    exact isUnit_add_of_injective_of_compact T (A-T) hunit hc (by simpa only [heq] using hinj)
  have hb (u : H) : min (a/2) 1*‖u‖^2 ≤ RCLike.re ⟪u,T u⟫_ℝ :=
    (mul_le_mul_of_nonneg_right (min_le_left (a/2) 1) (sq_nonneg ‖u‖)).trans (hT u)
  have hu' : IsUnit (T+(A-T)) := by simpa only [heq] using hu
  have hs := lp.eventually_isUnit_coerciveFiniteSection_add_compact T (A-T)
    (lt_min (half_pos ha) zero_lt_one) (min_le_right (a/2) 1) hb hc hu'
  have hn := lp.eventually_norm_inverse_coerciveFiniteSection_add_compact_le T (A-T)
    (lt_min (half_pos ha) zero_lt_one) (min_le_right (a/2) 1) hb hc hu'
  rw [heq] at hs hn
  exact ⟨hu,_,by positivity,hs.and hn⟩

private theorem reflection_square {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (P : E →L[ℝ] E) (hP : P*P=P) :
    (1-2*P)*(1-2*P) = 1 := by noncomm_ring [hP]

/-- A continuous nonvanishing diagonal, norm consistency and injectivity give stable sections. -/
theorem isUnit_and_stable_volterra_limit
    (K : (Fin 2 → ℝ) → ℝ) (p : ℕ → MvPolynomial (Fin 2) ℝ)
    (hK : ContinuousOn (fun x : ℝ ↦ K (fun _ ↦ x)) (Icc 0 1))
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, K (fun _ ↦ x) ≠ 0)
    {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n)
    (herr : ∀ n x, x ∈ Icc (0 : ℝ) 1 →
      |eval (fun _ ↦ x) (p n)-K (fun _ ↦ x)| ≤ e n)
    (hte : Tendsto e atTop (𝓝 0))
    (A : H →L[ℝ] H) (hA : Tendsto (fun n ↦ volterraPreconditionedL2 (p n)) atTop (𝓝 A))
    (hinj : Function.Injective A) :
    IsUnit A ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      IsUnit (coerciveFiniteSection (lp.initialL2Projection N) A) ∧
      ‖Ring.inverse (coerciveFiniteSection (lp.initialL2Projection N) A)‖ ≤ C := by
  have hb : ∃ a : ℝ, 0 < a ∧ ((∀ x ∈ Icc (0 : ℝ) 1, a ≤ K (fun _ ↦ x)) ∨
      (∀ x ∈ Icc (0 : ℝ) 1, a ≤ -K (fun _ ↦ x))) := by
    let f : ℝ → ℝ := fun x ↦ K (fun _ ↦ x)
    have hf : ContinuousOn f (Icc 0 1) := hK
    have hsign : (∀ x ∈ Icc (0 : ℝ) 1, 0 < f x) ∨ (∀ x ∈ Icc (0 : ℝ) 1, f x < 0) := by
      rcases lt_or_gt_of_ne (hd 0 (by simp)) with hn | hp
      · right
        intro x hx
        by_contra h
        obtain ⟨y,hy,he⟩ := intermediate_value_Icc hx.1 (hf.mono (fun y hy ↦ ⟨hy.1,hy.2.trans hx.2⟩))
          (show (0 : ℝ) ∈ Icc (f 0) (f x) from ⟨hn.le,le_of_not_gt h⟩)
        exact hd y ⟨hy.1,hy.2.trans hx.2⟩ he
      · left
        intro x hx
        by_contra h
        obtain ⟨y,hy,he⟩ := intermediate_value_Icc' hx.1 (hf.mono (fun y hy ↦ ⟨hy.1,hy.2.trans hx.2⟩))
          (show (0 : ℝ) ∈ Icc (f x) (f 0) from ⟨le_of_not_gt h,hp.le⟩)
        exact hd y ⟨hy.1,hy.2.trans hx.2⟩ he
    obtain ⟨t,ht,hm⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (0 : ℝ) 1).Nonempty from ⟨0,by simp⟩) hf.abs
    refine ⟨|f t|,abs_pos.mpr (hd t ht),?_⟩
    rcases hsign with hp | hn
    · left; intro x hx
      have hm' : |f t| ≤ |f x| := hm hx
      rwa [abs_of_pos (hp x hx)] at hm'
    · right; intro x hx
      have hm' : |f t| ≤ |f x| := hm hx
      rwa [abs_of_neg (hn x hx)] at hm'
  obtain ⟨a,ha,hp|hn⟩ := hb
  · exact positive_limit_stable K p he herr hte A hA hinj ha hp
  · have hneg : Tendsto (fun n ↦ volterraPreconditionedL2 (-p n)) atTop (𝓝 (-A)) := by
      simpa only [volterraPreconditionedL2_neg] using hA.neg
    obtain ⟨hu,C,hC,hs⟩ := positive_limit_stable (fun z ↦ -K z) (fun n ↦ -p n)
      he (fun n x hx ↦ by simpa only [map_neg, neg_sub_neg, abs_sub_comm] using herr n x hx)
      hte (-A) hneg (fun u v huv ↦ hinj (neg_injective huv)) ha hn
    refine ⟨by simpa only [neg_neg] using hu.neg,C*3,by positivity,?_⟩
    filter_upwards [hs] with N hN
    have hiN := (isUnit_coerciveFiniteSection_neg_iff _ _
      (lp.initialL2Projection_idempotent N)).mp hN.1
    refine ⟨hiN,?_⟩
    let P := lp.initialL2Projection (𝕜 := ℝ) N
    let Q : H →L[ℝ] H := 1-2*P
    have hP : P*P=P := lp.initialL2Projection_idempotent N
    have hQQ : Q*Q=1 := reflection_square P hP
    have hQ : IsUnit Q := isUnit_iff_exists.mpr ⟨Q,hQQ,hQQ⟩
    have hQi : Ring.inverse Q = Q := by
      calc
        _ = Ring.inverse Q * (Q*Q) := by rw [hQQ,mul_one]
        _ = Q := Ring.inverse_mul_cancel_left _ _ hQ
    have hnQ : ‖Q‖ ≤ 3 := by
      have heQ : Q = 1-P-P := by dsimp [Q]; noncomm_ring
      rw [heQ]
      have h1 := norm_sub_le (1 : H →L[ℝ] H) P
      have h2 := norm_sub_le (1-P) P
      have hpn := lp.norm_initialL2Projection_le (𝕜 := ℝ) N
      have hon := norm_id_le (𝕜 := ℝ) (E := H)
      change ‖P‖ ≤ 1 at hpn
      change ‖(1 : H →L[ℝ] H)‖ ≤ 1 at hon
      linarith
    have hs := coerciveFiniteSection_neg P (-A) hP
    rw [neg_neg] at hs
    rw [hs, Ring.inverse_mul (Or.inl hQ), hQi]
    exact (norm_mul_le _ _).trans (mul_le_mul hN.2 hnQ (norm_nonneg _) hC)

end MvPolynomial
