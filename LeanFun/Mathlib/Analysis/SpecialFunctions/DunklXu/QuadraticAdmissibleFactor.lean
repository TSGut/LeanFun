/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticPencilSection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.QuadraticPositive
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticCanonicalFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.DiskDeformation
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.GramFactorScaling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Admissible quadratic modifications without normalization
Positive scaling removes A+B=1 from the distant canonical-factor result.
All measure admissibility follows from A>=0, A+B>0, A+C>=0.
Reference: Cartesian disk deformation and uniqueness of Cholesky factors.
-/

public section
open MeasureTheory Set Polynomial Module Matrix Filter
open scoped Topology
namespace MvPolynomial

/-- Nonseparated admissible quadratics force distant canonical factor entries
for sufficiently small positive outer-factor deformations. -/
theorem eventually_integralGramFactor_admissible_quadratic_ne_zero {β : ℝ}
    (hβ : -1 < β) (A B C : ℝ) (hA : 0 ≤ A) (hAB : 0 < A + B) (hAC : 0 ≤ A + C) (hC : C ≠ 0) (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ δ in 𝓝[≠] (0 : ℝ), ∀ (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
      (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β)),
      let μ := cartesianDiskMeasure
        (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (ProductMeasureInput.ofSFinite (hν := by infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β))
      let ω := MvPolynomial.polynomialDensityMeasure ((coordinateQuadratic A B C)) ((μ).comap Subtype.val)
      ∀ (hM : MvPolynomial.HasFiniteMoments ω) (hP : MvPolynomial.HasPositiveDefiniteIntegral ω)
        {N : ℕ} {V : Submodule ℝ (MvPolynomial (Fin 2) ℝ)} (b : Basis (Fin N) ℝ V)
        (n k : Fin N → ℕ)
        (_hb : ∀ i, (b i : MvPolynomial (Fin 2) ℝ) = T.polynomial (n i) (k i))
        (e : DunklXuEvenInterior r ⊕ Fin (r + 1) → Fin N),
        Function.Injective e →
        (∀ i, n (e i) = 2 * (dunklXuEvenBlockCoordinates r i).1 +
          2 * (dunklXuEvenBlockCoordinates r i).2 ∧
          k (e i) = 2 * (dunklXuEvenBlockCoordinates r i).2) →
        (∀ i, (n i - k i) % 2 = 0 → k i % 2 = 0 → i ∈ Set.range e) →
        (∀ i j, e (Sum.inl i) < e (Sum.inr j)) → StrictMono (e ∘ Sum.inr) →
        integralGramFactor ω hM hP b (e (Sum.inr 0)) (e (Sum.inr (Fin.last r))) ≠ 0 := by
  have hnorm : A / (A + B) + B / (A + B) = 1 := by
    rw [← add_div, div_self hAB.ne']
  filter_upwards [eventually_integralGramFactor_deformed_quadratic_ne_zero hβ
    (A / (A + B)) (B / (A + B)) (C / (A + B)) hnorm
    (div_ne_zero hC hAB.ne') r hr] with δ ht
  intro hδ hδ1 T
  dsimp only
  intro hM hP N V b n k hb e he hlabels hcover hbefore hmono
  have hβ' : -1 < β + 1 / 2 := by linarith
  let := isFiniteMeasure_jacobiMeasure hβ' hβ'
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  have hx := ae_mem_Icc_diskDeformedMeasure hδ.le hδ1
    (ae_mem_Icc_jacobiMeasure (β + 1 / 2) (β + 1 / 2))
  have hz := ae_mem_Icc_jacobiMeasure β β
  have hA' := div_nonneg hA hAB.le
  have hAC' : 0 ≤ A / (A + B) + C / (A + B) := by
    rw [← add_div]
    exact div_nonneg hAC hAB.le
  have hu := ae_coordinateQuadratic_nonneg_cartesianDiskMeasure hx hz
    (A / (A + B)) (B / (A + B)) (C / (A + B)) hA' (by rw [hnorm]; norm_num) hAC'
  have hm := (hasFiniteMoments_cartesianDiskMeasure hx hz).withDensity_polynomial _ hu
  have hp := T.hasPositiveDefiniteIntegral_coordinateQuadratic hx hz
    (A / (A + B)) (B / (A + B)) (C / (A + B)) hA' (by rw [hnorm]; norm_num) hAC'
  have hn := ht hδ hδ1 (hasPositiveDefiniteIntegral_diskDeformed_jacobiMeasure
    hβ' hβ' hδ hδ1) T hu hm hp b n k hb e he hlabels hcover hbefore hmono
  have hscale : coordinateQuadratic A B C =
      (A + B) • coordinateQuadratic (A / (A + B)) (B / (A + B)) (C / (A + B)) := by
    simp only [coordinateQuadratic, smul_eq_C_mul, mul_add, ← mul_assoc, ← map_mul]
    field_simp
  intro hzR
  apply hn
  apply (integralGramFactor_eq_zero_iff_of_gram_scale _ _ hM hm hP hp b hAB ?_
    (e (Sum.inr 0)) (e (Sum.inr (Fin.last r)))).mp hzR
  · have hs := integralGram_withDensity_smul _ _
      (fun i => (b i : MvPolynomial (Fin 2) ℝ)) hu hAB.le
      (hi := fun _ _ => (T.hasFiniteMoments hx).integrable_mul _ _)
    ext i j
    have hij := congrFun (congrFun hs i) j
    dsimp only [integralGram, integralInner, IntegrablePair.of] at hij ⊢
    rw [hscale]
    exact hij

end MvPolynomial
