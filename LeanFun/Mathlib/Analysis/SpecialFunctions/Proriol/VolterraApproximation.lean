/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.IntegralEq.VolterraApproximation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraCoordinates
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-! # Convergence of finite Proriol Volterra assembly

Polynomial kernel and input approximations give uniformly convergent physical
outputs of the exact finite coefficient assembly. Reference: Gutleb–Olver,
arXiv:1906.03907, Sections 3.1–3.2.
-/

@[expose] public noncomputable section
open Set Polynomial Real Filter
open scoped Topology
namespace MvPolynomial

/-- Polynomial functions uniformly approximate a continuous function on a compact set. -/
theorem exists_polynomial_near_on_compact {S : Set (Fin 2 → ℝ)} (hS : IsCompact S)
    {f : (Fin 2 → ℝ) → ℝ} (hf : ContinuousOn f S) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 2) ℝ, ∀ z ∈ S, |eval z p-f z| < ε := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let A : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] C(S, ℝ) :=
    { toFun := fun p ↦ ⟨fun z ↦ eval z.1 p, p.continuous_eval.comp continuous_subtype_val⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp
      commutes' := by intro r; ext; simp }
  have hs : A.range.SeparatesPoints := by
    intro x y hxy
    have hne : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨A (X i), ⟨A (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
    simpa [A] using hi
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    A.range hs (fun z : S ↦ f z.1) (continuousOn_iff_continuous_domRestrict.mp hf) ε hε
  obtain ⟨p, hp⟩ := g.property
  refine ⟨p, fun z hz ↦ ?_⟩
  have h := hg ⟨z,hz⟩
  rw [← hp] at h
  simpa [A, Real.norm_eq_abs] using h

/-- The physical Volterra triangle is compact. -/
theorem isCompact_volterraTriangle : IsCompact volterraTriangle := by
  have he : volterraTriangle = Icc (0 : Fin 2 → ℝ) 1 ∩ {z | z 1 ≤ z 0} := by
    ext z
    constructor
    · intro ⟨hx, hy⟩
      refine ⟨⟨?_, ?_⟩, hy.2⟩
      · intro i; fin_cases i <;> simp_all
      · intro i; fin_cases i <;> simp_all; exact hy.2.trans hx.2
    · rintro ⟨⟨h0,h1⟩,hy⟩
      exact ⟨⟨h0 0,h1 0⟩,⟨h0 1,hy⟩⟩
  rw [he]
  exact isCompact_Icc.inter_right (isClosed_le (continuous_apply 1) (continuous_apply 0))

/-- Every continuous Volterra kernel has uniform polynomial approximants on its triangle. -/
theorem exists_polynomial_near_volterraKernel {K : (Fin 2 → ℝ) → ℝ}
    (hK : ContinuousOn K volterraTriangle) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 2) ℝ, ∀ z ∈ volterraTriangle, |eval z p-K z| < ε :=
  exists_polynomial_near_on_compact isCompact_volterraTriangle hK hε

/-- The finite coefficient assembly inherits the separate kernel and input error bound. -/
theorem volterraProriolCoefficients_error {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ}
    (hK : ContinuousOn K volterraTriangle) (hf : ContinuousOn f (Icc 0 1))
    (P : MvPolynomial (Fin 2) ℝ) (c : ℕ →₀ ℝ)
    {M F δ η : ℝ} (hM : 0 ≤ M) (hF : 0 ≤ F) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M) (bf : ∀ y ∈ Icc 0 1, |f y| ≤ F)
    (eK : ∀ z ∈ volterraTriangle, |eval z P-K z| ≤ δ)
    (ef : ∀ y ∈ Icc 0 1,
      |(Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c).eval y-f y| ≤ η)
    (x : Icc (0 : ℝ) 1) :
    |(x : ℝ) * (Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
      (volterraProriolCoefficients P c)).eval (1-(x : ℝ)) - volterraIntegral (VolterraIntegralInput.ofContinuous hK hf x)| ≤
      (δ*F+(M+δ)*η)*(x : ℝ) := by
  rw [volterraProriolCoefficients_exact]
  simpa only [VolterraIntegralInput.ofContinuous, volterraIntegral_ofKernel] using
    abs_volterraIntegral_sub_le hK P.continuous_eval.continuousOn hf
      (Polynomial.continuous _).continuousOn hM hF hδ hη bK bf eK ef x

/-- Vanishing polynomial approximation errors give uniform convergence of the
physical outputs assembled by `D M_K E`, including both endpoints. -/
theorem tendstoUniformly_volterraProriolCoefficients
    {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ}
    (hK : ContinuousOn K volterraTriangle) (hf : ContinuousOn f (Icc 0 1))
    (P : ℕ → MvPolynomial (Fin 2) ℝ) (c : ℕ → ℕ →₀ ℝ)
    {M F : ℝ} (hM : 0 ≤ M) (hF : 0 ≤ F)
    (bK : ∀ z ∈ volterraTriangle, |K z| ≤ M) (bf : ∀ y ∈ Icc 0 1, |f y| ≤ F)
    {δ η : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) (hη : ∀ n, 0 ≤ η n)
    (eK : ∀ n z, z ∈ volterraTriangle → |eval z (P n)-K z| ≤ δ n)
    (ef : ∀ n y, y ∈ Icc 0 1 →
      |(Finsupp.linearCombination ℝ (shiftedJacobi 1 0) (c n)).eval y-f y| ≤ η n)
    (tδ : Tendsto δ atTop (𝓝 0)) (tη : Tendsto η atTop (𝓝 0)) :
    TendstoUniformly (fun n (x : Icc (0 : ℝ) 1) ↦ (x : ℝ) * (Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
      (volterraProriolCoefficients (P n) (c n))).eval (1-(x : ℝ)))
      (fun x ↦ volterraIntegral (VolterraIntegralInput.ofContinuous hK hf x)) atTop := by
  simp_rw [volterraProriolCoefficients_exact]
  simpa only [VolterraIntegralInput.ofContinuous, volterraIntegral_ofKernel] using
    tendstoUniformly_volterraIntegral_of_error_bounds hK
    (fun n ↦ (P n).continuous_eval.continuousOn) hf
    (fun n ↦ (Polynomial.continuous _).continuousOn) hM hF bK bf hδ hη eK ef tδ tη

/-- Continuous data admit a finite coefficient assembly with any prescribed
uniform output tolerance; the kernel and input are approximated independently. -/
theorem exists_volterraProriolCoefficients_approximation
    {K : (Fin 2 → ℝ) → ℝ} {f : ℝ → ℝ}
    (hK : ContinuousOn K volterraTriangle) (hf : ContinuousOn f (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : MvPolynomial (Fin 2) ℝ) (c : ℕ →₀ ℝ), ∀ x : Icc (0 : ℝ) 1,
      |(x : ℝ) * (Finsupp.linearCombination ℝ (shiftedJacobi 1 0)
        (volterraProriolCoefficients P c)).eval (1-(x : ℝ)) - volterraIntegral (VolterraIntegralInput.ofContinuous hK hf x)| < ε := by
  obtain ⟨m, hm⟩ := isCompact_volterraTriangle.exists_bound_of_continuousOn hK
  obtain ⟨a, ha⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  let M := |m|
  let F := |a|
  have hM : 0 ≤ M := abs_nonneg _
  have hF : 0 ≤ F := abs_nonneg _
  have bK : ∀ z ∈ volterraTriangle, |K z| ≤ M := fun z hz ↦
    (hm z hz).trans (le_abs_self m)
  have bf : ∀ y ∈ Icc 0 1, |f y| ≤ F := fun y hy ↦
    (ha y hy).trans (le_abs_self a)
  let δ := min 1 (ε/(2*(F+M+1)))
  have hD : 0 < F+M+1 := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ*(F+M+1) ≤ ε/2 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right 1 (ε/(2*(F+M+1)))) hD.le
    dsimp [δ]
    convert h using 1
    field_simp
  obtain ⟨P, hP⟩ := exists_polynomial_near_volterraKernel hK hδ
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf δ hδ
  let S := shiftedJacobiSequence (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : (-1 : ℝ) < 0)
  let B := S.basis (fun n ↦ isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero n)))
  let c := B.repr p
  have hc : Finsupp.linearCombination ℝ (shiftedJacobi 1 0) c = p := by
    have he : (fun n ↦ B n) = shiftedJacobi 1 0 := by
      funext n
      simp [B, S]
    rw [← he]
    exact B.linearCombination_repr p
  refine ⟨P, c, fun x ↦ ?_⟩
  have he := volterraProriolCoefficients_error hK hf P c hM hF hδ.le hδ.le
    bK bf (fun z hz ↦ (hP z hz).le) (by simpa [hc] using fun y hy ↦ (hp y hy).le) x
  calc
    _ ≤ (δ*F+(M+δ)*δ)*(x : ℝ) := he
    _ ≤ δ*F+(M+δ)*δ := mul_le_of_le_one_right (by positivity) x.property.2
    _ ≤ δ*(F+M+1) := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
    _ ≤ ε/2 := hδε
    _ < ε := by linarith

end MvPolynomial
