/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.SeparatedCanonicalFactor
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.UniformInnerBandwidth
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Uniform canonical-factor bandwidth for separated modifications
Nonnegative separated polynomial factors give one bound over all admissible
Cartesian measures. Reference: separated Cartesian connection support.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial

/-- A separated nonnegative density is nonnegative for the disk pushforward. -/
theorem ae_nonneg_cartesianDiskModification {μ ν : Measure ℝ} [SFinite ν]
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) (h g : ℝ[X]) (l : ℕ)
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (hg : ∀ᵐ z ∂ν, 0 ≤ g.eval z)
    (hgdeg : g.natDegree ≤ 2 * l) (hgcoeff : ∀ i, i % 2 ≠ 0 → g.coeff i = 0) :
    ∀ᵐ v ∂cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) (ProductMeasureInput.ofSFinite (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν), 0 ≤ eval v (cartesianDiskModification h g l) := by
  have hw : ∀ᵐ x : Icc (-1 : ℝ) 1 ∂μ.comap Subtype.val,
      0 ≤ (diskModificationWeight h l).eval (x : ℝ) := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le measurable_const (diskModificationWeight h l).continuous.measurable)).mp
    rw [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem hx]
    exact diskModificationWeight_nonneg hx h hh l
  unfold cartesianDiskMeasure
  apply (ae_map_iff continuous_diskCoordinates.measurable.aemeasurable
    (measurableSet_le measurable_const (cartesianDiskModification h g l).continuous_eval.measurable)).2
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hw,
    Measure.quasiMeasurePreserving_snd.ae hg] with v hv hg'
  change 0 ≤ eval (![ (v.1 : ℝ), Real.sqrt (1-(v.1 : ℝ)^2)*v.2])
    (cartesianDiskModification h g l)
  rw [eval_cartesianDiskModification h g l hgdeg hgcoeff (v.1 : ℝ) v.2 v.1.property]
  exact mul_nonneg hv hg'

/-- Separated nonnegative polynomial factors give a uniform canonical inner bandwidth. -/
theorem hasUniformCartesianInnerBandwidth_separated (h g : ℝ[X]) (l : ℕ)
    (hh0 : h ≠ 0) (hg0 : g ≠ 0)
    (hh : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ h.eval x)
    (hg : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ g.eval x)
    (hgpar : ∀ x, g.eval (-x) = g.eval x)
    (hgcoeff : ∀ i, i % 2 ≠ 0 → g.coeff i = 0) (hgdeg : g.natDegree ≤ 2 * l) :
    HasUniformCartesianInnerBandwidth (cartesianDiskModification h g l) := by
  refine ⟨g.natDegree, ?_⟩
  intro μ ν _ _ _ hμ hpμ hν hpν hx hz S N hu
  dsimp only
  intro hM hP i j hgap
  have hh' : ∀ᵐ x ∂μ, 0 ≤ h.eval x := hx.mono (fun x hx ↦ hh x hx)
  have hg' : ∀ᵐ x ∂ν, 0 ≤ g.eval x := hz.mono (fun x hz ↦ hg x hz)
  exact S.integralGramFactor_eq_zero_of_separated_inner_gap hμ hpμ hν hpν hx hz h g l
    hh0 hg0 hh' hg' hgpar hgcoeff hgdeg _
    (ae_nonneg_cartesianDiskModification hx h g l hh' hg' hgdeg hgcoeff) rfl hM hP N i j hgap

end MvPolynomial
