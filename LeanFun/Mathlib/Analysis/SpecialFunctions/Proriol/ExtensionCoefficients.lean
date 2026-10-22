/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.Coordinates
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.MarginalCoefficients
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Proriol.VolterraPolynomial

/-! # Exact finite Proriol extension coordinates

Finite-basis coordinates define the complete inner-variable extension, not just
its marginal. Reflection and sign normalization match the Volterra basis.
Reference: Gutleb–Olver, arXiv:1906.03907, Section 3.1.
The explicit rational entry formula is a separate result.
-/

@[expose] public noncomputable section
namespace MvPolynomial
open Polynomial

/-- Transport finite DLMF coordinates into reflected, signed Volterra coordinates. -/
def proriolVolterraCoordinateTransport (N : ℕ) :
    ({d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} →₀ ℝ) →ₗ[ℝ]
      ((Σ n : ℕ, Fin (n+1)) →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun d ↦
    Finsupp.single ⟨d.1 0+d.1 1, ⟨d.1 1, by omega⟩⟩ ((-1 : ℝ)^(d.1 0)))

/-- Transport followed by synthesis is reflection of the original synthesis. -/
theorem proriolVolterraSynthesis_transport (N : ℕ)
    (c : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} →₀ ℝ) :
    proriolVolterraSynthesis (proriolVolterraCoordinateTransport N c) =
      triangleReflect (Finsupp.linearCombination ℝ
        (fun d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ↦
          proriol 0 0 0 (d.1 0+d.1 1) (d.1 1)) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single d a =>
    rw [proriolVolterraCoordinateTransport, Finsupp.linearCombination_single,
      map_smul, proriolVolterraSynthesis, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single]
    simp only [Nat.add_sub_cancel, smul_smul, map_smul]
    have hs : (-1 : ℝ)^(d.1 0) * (-1 : ℝ)^(d.1 0) = 1 := by
      rw [← mul_pow]; simp
    rw [hs, mul_one]

/-- Coordinate transport introduces no degrees above the finite cutoff. -/
theorem proriolVolterraCoordinateTransport_eq_zero (N : ℕ)
    (c : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} →₀ ℝ)
    (i : Σ n : ℕ, Fin (n+1)) (hi : N < i.1) :
    proriolVolterraCoordinateTransport N c i = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single d a =>
    rw [proriolVolterraCoordinateTransport, Finsupp.linearCombination_single]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    have hn : (⟨d.1 0+d.1 1, ⟨d.1 1, by omega⟩⟩ : Σ n : ℕ, Fin (n+1)) ≠ i := by
      intro he
      have he' := congrArg Sigma.fst he
      have hd := d.2
      rw [sum_exponents_fin_two] at hd
      dsimp only at he'
      omega
    rw [Finsupp.single_eq_of_ne (Ne.symm hn), mul_zero]

/-- Exact coefficients of inner-variable extension through degree `N`. -/
def proriolExtensionCoefficients (N : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ N) :
    (Σ n : ℕ, Fin (n+1)) →₀ ℝ :=
  proriolVolterraCoordinateTransport N
    ((proriolDegreeBasis (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) N).repr
        ⟨triangleExtendY p, (mem_restrictTotalDegree (Fin 2) N _).mpr
          ((totalDegree_eval₂_C_X_le p (1 : Fin 2)).trans hp)⟩)

/-- Reflection in the outer coordinate leaves an inner-variable extension fixed. -/
theorem triangleReflect_extendY (p : ℝ[X]) :
    triangleReflect (triangleExtendY p) = triangleExtendY p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a =>
    simp [triangleExtendY, Polynomial.aeval_def, Polynomial.eval₂_monomial,
      triangleReflect, aeval_def]

/-- Outer reflection is its own inverse on triangle polynomials. -/
theorem triangleReflect_involutive : Function.Involutive triangleReflect := by
  have h0 : triangleReflect (X 0) = 1-X 0 := by simp [triangleReflect, aeval_def]
  have h1 : triangleReflect (X 1) = X 1 := by simp [triangleReflect, aeval_def]
  have h : triangleReflect.comp triangleReflect = AlgHom.id ℝ _ := by
    ext i : 1
    change triangleReflect (triangleReflect (X i)) = X i
    fin_cases i
    · change triangleReflect (triangleReflect (X 0)) = X 0
      rw [h0, map_sub, map_one, h0, sub_sub_cancel]
    · change triangleReflect (triangleReflect (X 1)) = X 1
      rw [h1, h1]
  intro p
  exact congrArg (fun f : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ ↦ f p) h

/-- Finite expansions in the signed Volterra basis are unique. -/
theorem proriolVolterraSynthesis_injective : Function.Injective proriolVolterraSynthesis := by
  have hv := proriol_linearIndependent (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0)
  have hs := hv.units_smul (fun i : Σ n : ℕ, Fin (n+1) ↦ (-1 : ℝˣ)^(i.1-i.2.val))
  have hm := hs.map' triangleReflect.toLinearMap
    (LinearMap.ker_eq_bot.mpr triangleReflect_involutive.injective)
  have hf : (triangleReflect.toLinearMap ∘
      (fun i : Σ n : ℕ, Fin (n+1) ↦
        (-1 : ℝˣ)^(i.1-i.2.val) • proriol 0 0 0 i.1 i.2)) =
      (fun i : Σ n : ℕ, Fin (n+1) ↦
        (-1 : ℝ)^(i.1-i.2.val) • triangleReflect (proriol 0 0 0 i.1 i.2)) := by
    funext i
    change triangleReflect ((-1 : ℝ)^(i.1-i.2.val) • proriol 0 0 0 i.1 i.2) = _
    rw [map_smul]
  change LinearIndependent ℝ (triangleReflect.toLinearMap ∘
    (fun i : Σ n : ℕ, Fin (n+1) ↦
      (-1 : ℝˣ)^(i.1-i.2.val) • proriol 0 0 0 i.1 i.2)) at hm
  change LinearIndependent ℝ (fun i : Σ n : ℕ, Fin (n+1) ↦
    (-1 : ℝ)^(i.1-i.2.val) • triangleReflect (proriol 0 0 0 i.1 i.2))
  exact hf ▸ hm

/-- Synthesizing all extension coordinates recovers the polynomial exactly. -/
theorem proriolVolterraSynthesis_extension (N : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ N) :
    proriolVolterraSynthesis (proriolExtensionCoefficients N p hp) = triangleExtendY p := by
  let b := proriolDegreeBasis (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) N
  let q : restrictTotalDegree (Fin 2) ℝ N :=
    ⟨triangleExtendY p, (mem_restrictTotalDegree (Fin 2) N _).mpr
      ((totalDegree_eval₂_C_X_le p (1 : Fin 2)).trans hp)⟩
  have h := congrArg (fun t : restrictTotalDegree (Fin 2) ℝ N ↦
    (t : MvPolynomial (Fin 2) ℝ)) (b.linearCombination_repr q)
  have he : Finsupp.linearCombination ℝ
      (fun d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ↦
        proriol 0 0 0 (d.1 0+d.1 1) (d.1 1)) (b.repr q) = triangleExtendY p := by
    have hf : (fun d ↦ (b d : MvPolynomial (Fin 2) ℝ)) =
        (fun d : {d : Fin 2 →₀ ℕ // d.sum (fun _ e ↦ e) ≤ N} ↦
          proriol 0 0 0 (d.1 0+d.1 1) (d.1 1)) := by
      funext d
      exact proriolDegreeBasis_apply _ _ _ N d
    change (↑((b.repr q).sum (fun i a ↦ a • b i)) : MvPolynomial (Fin 2) ℝ) = _ at h
    simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← hf, Finsupp.linearCombination_apply]
    exact h
  rw [proriolExtensionCoefficients, proriolVolterraSynthesis_transport]
  change triangleReflect (Finsupp.linearCombination ℝ _ (b.repr q)) = _
  rw [he, triangleReflect_extendY]

/-- Pointwise correctness on every real pair, including the triangle boundary. -/
theorem eval_proriolVolterraSynthesis_extension (N : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ N) (x y : ℝ) :
    eval (![x,y] : Fin 2 → ℝ)
      (proriolVolterraSynthesis (proriolExtensionCoefficients N p hp)) = p.eval y := by
  rw [proriolVolterraSynthesis_extension, eval_triangleExtendY]

/-- The complete extension has no coefficients above the input degree bound. -/
theorem proriolExtensionCoefficients_eq_zero (N : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ N) (i : Σ n : ℕ, Fin (n+1)) (hi : N < i.1) :
    proriolExtensionCoefficients N p hp i = 0 :=
  proriolVolterraCoordinateTransport_eq_zero N _ i hi

/-- Extension followed by the finite marginal coefficient operator gives the
actual simplex integral, with the endpoint factor included. -/
theorem eval_proriolMarginalPolynomial_extension (N : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ N) (x : ℝ) :
    (proriolMarginalPolynomial (proriolExtensionCoefficients N p hp)).eval x =
      ∫ y in (0 : ℝ)..(1-x), p.eval y := by
  rw [eval_proriolMarginalPolynomial, proriolVolterraSynthesis_extension]
  change (∫ y in (0 : ℝ)..(1-x), eval (![x,y] : Fin 2 → ℝ) (triangleExtendY p)) = _
  simp only [eval_triangleExtendY]

/-- The coefficient vector is independent of any larger ambient degree cutoff. -/
theorem proriolExtensionCoefficients_cutoff (N M : ℕ) (p : ℝ[X])
    (hN : p.natDegree ≤ N) (hM : p.natDegree ≤ M) :
    proriolExtensionCoefficients N p hN = proriolExtensionCoefficients M p hM := by
  apply proriolVolterraSynthesis_injective
  rw [proriolVolterraSynthesis_extension, proriolVolterraSynthesis_extension]

/-- Extension coordinates are additive for any common admissible degree cutoff. -/
theorem proriolExtensionCoefficients_add (N : ℕ) (p q : ℝ[X])
    (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N) :
    proriolExtensionCoefficients N (p+q) (natDegree_add_le_of_degree_le hp hq) =
      proriolExtensionCoefficients N p hp + proriolExtensionCoefficients N q hq := by
  apply proriolVolterraSynthesis_injective
  simp only [map_add, proriolVolterraSynthesis_extension]

/-- Extension coordinates commute with scalar multiplication. -/
theorem proriolExtensionCoefficients_smul (N : ℕ) (a : ℝ) (p : ℝ[X])
    (hp : p.natDegree ≤ N) :
    proriolExtensionCoefficients N (a • p) ((natDegree_smul_le a p).trans hp) =
      a • proriolExtensionCoefficients N p hp := by
  apply proriolVolterraSynthesis_injective
  simp only [map_smul, proriolVolterraSynthesis_extension]

end MvPolynomial
