/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.RingTheory.MvPolynomial.DunklXu
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Coordinates
public import LeanFun.Mathlib.Analysis.SpecialFunctions.Jacobi.Norm
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Multivariate.InnerProduct
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp

/-!
# Cartesian coordinates for the Dunkl–Xu disk measure

The map `(x,z) ↦ (x, sqrt(1-x²) z)` transports the separated Jacobi measures
onto the disk. The change of variables to the usual radial density is a separate
identity; the definition does not identify the square with the disk.

Reference: Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, disk families.
-/

@[expose] public section
open MeasureTheory Set Polynomial
open scoped NNReal ENNReal
attribute [local instance] Measure.Subtype.measureSpace
namespace MvPolynomial

theorem sFinite_jacobiMeasure (α β : ℝ) : SFinite (jacobiMeasure α β) := by
  classical
  let g : ℝ → ℝ≥0∞ := fun x ↦ if h : x ∈ Ioo (-1 : ℝ) 1 then
    (jacobiWeight α β ⟨x, h⟩ : ℝ≥0∞) else 0
  have hg : Measurable g :=
    ((measurable_jacobiWeight α β).coe_nnreal_ennreal).dite measurable_const measurableSet_Ioo
  have hm : jacobiMeasure α β = (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity g := by
    apply openIntervalWeightMeasure_eq _ _ _ _ hg
    intro x
    simp only [g, dite_eq_left x.property]
  rw [hm]
  infer_instance

/-- The separated-coordinate disk measure in Jacobi normalization. -/
noncomputable def dunklXuDiskMeasure (β : ℝ) : Measure (Fin 2 → ℝ) := by
  let : SFinite (jacobiMeasure β β) := sFinite_jacobiMeasure β β
  exact cartesianDiskMeasure (Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
    (jacobiMeasure (β+1/2) (β+1/2))) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
    (jacobiMeasure (β+1/2) (β+1/2))) (jacobiMeasure β β))

/-- Finite mass throughout the disk orthogonality range. -/
theorem isFiniteMeasure_dunklXuDiskMeasure {β : ℝ} (hβ : -1 < β) :
    IsFiniteMeasure (dunklXuDiskMeasure β) := by
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isFiniteMeasure_jacobiMeasure
    (show -1 < β + 1 / 2 by linarith) (show -1 < β + 1 / 2 by linarith)
  unfold dunklXuDiskMeasure cartesianDiskMeasure
  infer_instance

/-- The polynomial construction agrees with the separated expression on each
vertical slice, with no restriction on the second parameter. -/
theorem eval_dunklXuDisk_diskCoordinates (β : ℝ) (n k : ℕ) (x z : ℝ)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    eval ((fun v : ℝ × ℝ ↦ (![v.1, Real.sqrt (1-v.1^2)*v.2] : Fin 2 → ℝ)) (x, z)) (dunklXuDisk β n k) =
      (jacobi (β + k + 1 / 2) (β + k + 1 / 2) (n - k)).eval x *
      Real.sqrt (1 - x ^ 2) ^ k * (jacobi β β k).eval z := by
  have hsq : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  rw [eval_dunklXuDisk β n k _ (by simpa [] using hsq)]
  simp [ hs, mul_assoc]

/-- A continuous function on the plane is integrable for the disk measure. -/
theorem integrable_dunklXuDiskMeasure {β : ℝ} (hβ : -1 < β)
    {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (dunklXuDiskMeasure β) := by
  let := isFiniteMeasure_jacobiMeasure hβ hβ
  let := isFiniteMeasure_jacobiMeasure
    (show -1 < β + 1 / 2 by linarith) (show -1 < β + 1 / 2 by linarith)
  change Integrable f (Measure.map diskCoordinates
    ((Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
      (jacobiMeasure (β + 1/2) (β + 1/2))).prod (jacobiMeasure β β)))
  rw [integrable_map_measure hf.aestronglyMeasurable
    continuous_diskCoordinates.measurable.aemeasurable]
  have hi := (hf.comp continuous_diskCoordinates).continuousOn.integrableOn_compact
    (μ := (Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
      (jacobiMeasure (β + 1/2) (β + 1/2))).prod (jacobiMeasure β β))
    (isCompact_univ.prod isCompact_Icc :
      IsCompact (univ ×ˢ Icc (-1 : ℝ) 1 : Set (Icc (-1 : ℝ) 1 × ℝ)))
  have ha : ∀ᵐ v ∂(Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
      (jacobiMeasure (β + 1/2) (β + 1/2))).prod (jacobiMeasure β β),
      v ∈ (univ ×ˢ Icc (-1 : ℝ) 1 : Set (Icc (-1 : ℝ) 1 × ℝ)) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_mem_Ioo_jacobiMeasure β β)] with v hz
    exact ⟨mem_univ _, hz.1.le, hz.2.le⟩
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi

/-- All polynomial moments exist in the disk orthogonality range. -/
@[aesop (rule_sets := [PolynomialIntegrability]) unsafe 80% apply]
theorem hasFiniteMoments_dunklXuDiskMeasure {β : ℝ} (hβ : -1 < β) :
    HasFiniteMoments (dunklXuDiskMeasure β) := by
  intro p
  exact integrable_dunklXuDiskMeasure hβ (p.continuous_eval.pow 2)

attribute [local instance] Measure.Subtype.measureSpace

/-- Separated disk coordinates with the radius evaluated only in the open strip. -/
theorem dunklXuDiskMeasure_eq_map_open (β : ℝ) :
    dunklXuDiskMeasure β = Measure.map
      (fun v : Ioo (-1 : ℝ) 1 × ℝ ↦
        (![v.1, Real.sqrt (1 - (v.1 : ℝ)^2) * v.2] : Fin 2 → ℝ))
      ((volume.withDensity fun x : Ioo (-1 : ℝ) 1 ↦
        (jacobiWeight (β + 1/2) (β + 1/2) x : ℝ≥0∞)).prod (jacobiMeasure β β)) := by
  let : SFinite (jacobiMeasure β β) := sFinite_jacobiMeasure β β
  let ι : Ioo (-1 : ℝ) 1 → Icc (-1 : ℝ) 1 := fun x ↦ ⟨x, x.property.1.le, x.property.2.le⟩
  have hι : Measurable ι := by fun_prop
  have hm : Measure.comap (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
      (jacobiMeasure (β + 1/2) (β + 1/2)) =
      Measure.map ι (volume.withDensity fun x : Ioo (-1 : ℝ) 1 ↦
        (jacobiWeight (β + 1/2) (β + 1/2) x : ℝ≥0∞)) := by
    apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
    rw [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem
        ((ae_mem_Ioo_jacobiMeasure (β + 1/2) (β + 1/2)).mono
          (fun _ hx ↦ (show _ ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2.le⟩))),
      Measure.map_map measurable_subtype_coe hι]
    rfl
  change Measure.map diskCoordinates ((Measure.comap
    (Subtype.val : Icc (-1 : ℝ) 1 → ℝ)
    (jacobiMeasure (β + 1/2) (β + 1/2))).prod (jacobiMeasure β β)) = _
  rw [hm]
  conv_lhs => arg 2; arg 2; rw [← Measure.map_id (μ := jacobiMeasure β β)]
  rw [Measure.map_prod_map _ _ hι measurable_id,
    Measure.map_map continuous_diskCoordinates.measurable (hι.prodMap measurable_id)]
  rfl

/-- Polynomial pullback through the classical open-strip coordinates. -/
theorem integral_dunklXuDiskMeasure_open (β : ℝ)
    (f : IntegrableInput (dunklXuDiskMeasure β)) :
    (∫ v, f.val v ∂dunklXuDiskMeasure β) =
      ∫ v : Ioo (-1 : ℝ) 1 × ℝ,
        f.val (![v.1, Real.sqrt (1 - (v.1 : ℝ)^2) * v.2])
        ∂((volume.withDensity fun x : Ioo (-1 : ℝ) 1 ↦
          (jacobiWeight (β + 1/2) (β + 1/2) x : ℝ≥0∞)).prod
            (jacobiMeasure β β)) := by
  rcases f with ⟨f, hf⟩
  dsimp only [Subtype.coe_mk]
  rw [dunklXuDiskMeasure_eq_map_open] at hf ⊢
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

end MvPolynomial
