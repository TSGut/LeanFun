/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.System
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.Modification
public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.ConnectionSupport

/-!
# Connection support for separated Cartesian disk modifications

Inner and outer orthogonality bound the two index gaps independently. These are
exact vanishing statements, not estimates obtained by numerical thresholding.
Reference: Dunkl–Xu, Cartesian constructions; Gutleb–Olver–Slevinsky,
polynomial measure modification and connection factors.
-/

@[expose] public section
open MeasureTheory Set Polynomial
namespace MvPolynomial.CartesianDiskSystem

/-- A source polynomial's coefficient against an orthonormal target polynomial. -/
noncomputable def connectionEntry {μ ν μ' ν' : Measure ℝ}
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') ν')
    (n k m j : ℕ)
    (hi : Integrable (fun x => eval x (S.polynomial n k) * eval x (T.polynomial m j))
      (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') (ProductMeasureInput.ofSFinite (hν := by let := T.hasFiniteMoments_inner.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') ν')) := by
      aesop (config := { enableSimp := false }) (rule_sets := [PolynomialIntegrability])) : ℝ :=
  integralInner (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') (ProductMeasureInput.ofSFinite (hν := by let := T.hasFiniteMoments_inner.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') ν')) (IntegrablePair.of (cartesianDiskMeasure (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') (ProductMeasureInput.ofSFinite (hν := by let := T.hasFiniteMoments_inner.isFiniteMeasure; infer_instance) (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ') ν')) (S.polynomial n k) (T.polynomial m j))

variable {μ ν : Measure ℝ}
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (h g : ℝ[X]) (l : ℕ)
    (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))
    (hμ : Polynomial.HasFiniteMoments μ) (hν : Polynomial.HasFiniteMoments ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (hg : ∀ᵐ x ∂ν, 0 ≤ g.eval x)

include hμ hν hx hh hg

/-- Only the inner bandwidth of the modifying polynomial can occur. -/
theorem connectionEntry_eq_zero_of_inner_band {n k m j : ℕ}
    (hout : k < j ∨ j+g.natDegree < k) : S.connectionEntry T n k m j = 0 := by
  let := (hμ.diskOuterModification hx h hh l).isFiniteMeasure
  let := (hν.polynomialDensityMeasure g hg).isFiniteMeasure
  dsimp only [connectionEntry, polynomial]
  rw [
    integralInner_cartesianDiskPolynomial (ae_mem_diskOuterModification hx h l)
      _ _ _ _ k j (by simp) (by simp) (S.inner_parity k) (T.inner_parity j),
    S.inner_orthogonal.integralInner_eq_zero_of_polynomial_modification hν g hg
      T.inner_orthogonal hout, mul_zero]

/-- An even inner gap expresses the coefficient as a polynomial outer pairing. -/
theorem connectionEntry_of_degree_gap (n k m j r : ℕ) (hkj : k=j+2*r) :
    S.connectionEntry T n k m j =
      Polynomial.integralInner (diskOuterMeasure j ((diskOuterModification h l (μ.comap Subtype.val)).comap Subtype.val)) (Polynomial.IntegrablePair.of (diskOuterMeasure j ((diskOuterModification h l (μ.comap Subtype.val)).comap Subtype.val)) ((1-Polynomial.X^2)^r*S.outer k (n-k)) (T.outer j (m-j))) *
      Polynomial.integralInner (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)) (Polynomial.IntegrablePair.of (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)) (S.inner k) (T.inner j)) := by
  let := (hμ.diskOuterModification hx h hh l).isFiniteMeasure
  let := (hν.polynomialDensityMeasure g hg).isFiniteMeasure
  exact integralInner_cartesianDiskPolynomial_of_degree_gap
    (ae_mem_diskOuterModification hx h l) _ _ _ _ k j r hkj
    (by simp) (by simp) (S.inner_parity k) (T.inner_parity j)

/-- The outer bandwidth is bounded independently of the source degree. -/
theorem connectionEntry_eq_zero_of_outer_band {n k m j r : ℕ}
    (hk : k ≤ n) (hj : j ≤ m) (hkj : k=j+2*r) (hr : r ≤ l)
    (hout : n < m ∨ m+h.natDegree+2*l < n) : S.connectionEntry T n k m j = 0 := by
  rw [S.connectionEntry_of_degree_gap h g l T hμ hν hx hh hg n k m j r hkj]
  have hd (t : ℕ) : ((1-Polynomial.X^2 : ℝ[X])^t).natDegree ≤ 2*t := by
    rw [natDegree_pow]
    have hb : (1-Polynomial.X^2 : ℝ[X]).natDegree ≤ 2 :=
      (natDegree_sub_le _ _).trans (by simp)
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right t hb
  rcases hout with hout | hout
  · have hd' : ((1-Polynomial.X^2)^r*S.outer k (n-k)).natDegree < m-j := by
      have hb := natDegree_mul_le (p := (1-Polynomial.X^2 : ℝ[X])^r)
        (q := S.outer k (n-k))
      rw [Sequence.natDegree_eq] at hb
      have := hd r
      omega
    rw [(T.outer_orthogonal_real j).integralInner_eq_zero_of_degree_lt
      ((hμ.diskOuterModification hx h hh l).diskOuterMeasure
        (ae_mem_diskOuterModification hx h l) j)
      (degree_le_natDegree.trans_lt (by exact_mod_cast hd')), zero_mul]
  · rw [integralInner_diskOuterModification_transfer hx h hh _ _ l j k r hr hkj,
      Polynomial.integralInner_comm]
    have hd' : (((1-Polynomial.X^2)^(l-r)*h)*T.outer j (m-j)).natDegree < n-k := by
      have hb := natDegree_mul_le (p := ((1-Polynomial.X^2 : ℝ[X])^(l-r)*h))
        (q := T.outer j (m-j))
      have hc := natDegree_mul_le (p := (1-Polynomial.X^2 : ℝ[X])^(l-r)) (q := h)
      rw [Sequence.natDegree_eq] at hb
      have := hd (l-r)
      omega
    rw [(S.outer_orthogonal_real k).integralInner_eq_zero_of_degree_lt
      (hμ.diskOuterMeasure hx k)
      (degree_le_natDegree.trans_lt (by exact_mod_cast hd')), zero_mul]

end MvPolynomial.CartesianDiskSystem
