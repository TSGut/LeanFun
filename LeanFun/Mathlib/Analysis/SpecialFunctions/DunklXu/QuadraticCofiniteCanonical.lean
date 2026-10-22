/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticPencilSection
public import LeanFun.Mathlib.Analysis.SpecialFunctions.DunklXu.QuadraticPointwiseFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.QuadraticReflection

/-! # Distant entries in the canonical deformed-measure factor
For a normalized nonseparated diagonal quadratic, every requested even degree
has a nonzero distant entry outside a finite set of deformation parameters.
The result is stated for any complete sector enumeration respecting the existing
degree/inner order, and uses the canonical integralGramFactor itself.
Reference: Cartesian disk deformation and Cholesky measure modification.
-/

public section
open MeasureTheory Set Polynomial Module Matrix Filter
open scoped Topology
namespace MvPolynomial

/-- Canonical full-factor nonvanishing for actual deformed Cartesian measures.
The nonnegative quadratic is normalized by A+B=1. The source finite basis and
its complete even-sector embedding retain their explicit ordering hypotheses. -/
theorem eventually_cofinite_integralGramFactor_deformed_quadratic_ne_zero {β : ℝ}
    (hβ : -1 < β) (A B C : ℝ) (hAB : A + B = 1) (hC : C ≠ 0) (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ δ in Filter.cofinite, ∀ (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
      (_hδpos : Polynomial.HasPositiveDefiniteIntegral
        (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val)))
      (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β)),
      let μ := cartesianDiskMeasure
        (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (ProductMeasureInput.ofSFinite (hν := by infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskDeformedMeasure δ ((jacobiMeasure (β + 1 / 2) (β + 1 / 2)).comap Subtype.val))) (jacobiMeasure β β))
      let ω := MvPolynomial.polynomialDensityMeasure ((coordinateQuadratic A B C)) ((μ).comap Subtype.val)
      ∀ (_hu : ∀ᵐ x ∂μ, 0 ≤ eval x (coordinateQuadratic A B C))
        (hM : MvPolynomial.HasFiniteMoments ω) (hP : MvPolynomial.HasPositiveDefiniteIntegral ω)
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
  filter_upwards [eventually_cofinite_dunklXu_full_factor_entry_ne_zero hβ B C hC r hr] with δ ht
  intro hδ hδ1 hδpos T
  dsimp only
  intro hu hM hP N V b n k hb e he hlabels hcover hbefore hmono
  have hβ' : -1 < β + 1 / 2 := by linarith
  let := isFiniteMeasure_jacobiMeasure hβ' hβ'
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isNegInvariant_jacobiMeasure β
  have hx := ae_mem_Icc_diskDeformedMeasure hδ.le hδ1 (ae_mem_Icc_jacobiMeasure (β + 1 / 2) (β + 1 / 2))
  have hm := hasFiniteMoments_diskDeformedMeasure hδ.le hδ1 (ae_mem_Icc_jacobiMeasure (β + 1 / 2) (β + 1 / 2))
  obtain ⟨hR, hd, hg⟩ := integralGramFactor_spec _ hM hP b
  refine ht (integralGramFactor _ hM hP b) (fun i ↦ ((n i - k i) % 2, k i % 2)) e (0, 0)
    hR (fun i ↦ (hd i).ne') ?_ he ?_ ?_ hbefore hmono ?_
  · intro i j hij
    rw [← hg]
    change integralInner _ (IntegrablePair.of _ (b i : MvPolynomial (Fin 2) ℝ) (b j : MvPolynomial (Fin 2) ℝ) (h := hM.integrable_mul _ _)) = 0
    simp only [hb]
    rw [MvPolynomial.integralInner_withDensity_polynomial _ _ _ hu
      (hpq := (T.hasFiniteMoments hx).integrable_mul _ _)]
    exact T.integralInner_coordinateQuadratic_eq_zero_of_parity hx hm hδpos A B C _ _ _ _ hij
  · intro i
    rw [(hlabels i).1, (hlabels i).2]
    apply Prod.ext <;> dsimp <;> omega
  · intro i hi
    exact hcover i (congrArg Prod.fst hi) (congrArg Prod.snd hi)
  · ext i j
    rw [Matrix.submatrix_apply, ← hg]
    change integralInner _ (IntegrablePair.of _ (b (e i) : MvPolynomial (Fin 2) ℝ) (b (e j) : MvPolynomial (Fin 2) ℝ) (h := hM.integrable_mul _ _)) = _
    simp only [hb, (hlabels i).1, (hlabels i).2, (hlabels j).1, (hlabels j).2]
    exact integralInner_deformed_quadratic_eq_evenGramPencil hβ hδ hδ1 hδpos T A B C hAB hu r i j

end MvPolynomial
