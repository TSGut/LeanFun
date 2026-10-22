/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Disk.ConnectionParity

/-!
# Exact rectangular support for separated disk modifications

For a modification (1-x²)^l h(x) g(z), with degrees bounded by 2a and 2l,
only the offsets (2s,2r), s≤a+l and r≤l, can occur. The result is uniform
in total degree and admits additional zeros inside the permitted set.
Reference: the Cartesian reduction of Dunkl–Xu and polynomial measure-conversion
orthogonality as in Gutleb–Olver–Slevinsky.
-/

public section
open MeasureTheory Set Polynomial
namespace MvPolynomial.CartesianDiskSystem
variable {μ ν : Measure ℝ}
    (S : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) μ) ν) (h g : ℝ[X]) (l : ℕ)
    (T : CartesianDiskSystem (Measure.comap (Subtype.val : Set.Icc (-1 : ℝ) 1 → ℝ) (diskOuterModification h l (μ.comap Subtype.val)))
      (Polynomial.polynomialDensityMeasure (g) ((ν).comap Subtype.val)))
    (hμ : Polynomial.HasFiniteMoments μ) (hν : Polynomial.HasFiniteMoments ν)
    (hx : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1)
    (hh : ∀ᵐ x ∂μ, 0 ≤ h.eval x) (hg : ∀ᵐ x ∂ν, 0 ≤ g.eval x)

include hμ hν hx hh hg

/-- Without outer reflection symmetry, the same mechanism bounds all total-degree
steps while retaining the even inner-degree steps. -/
theorem connectionEntry_eq_zero_of_outside_band [ν.IsNegInvariant]
    (hgpar : ∀ x, g.eval (-x) = g.eval x) (hgdeg : g.natDegree ≤ 2*l)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hout : ¬ ∃ s r : ℕ, s ≤ h.natDegree+2*l ∧ r ≤ l ∧ n=m+s ∧ k=j+2*r) :
    S.connectionEntry T n k m j = 0 := by
  by_cases hb : k < j ∨ j+g.natDegree < k
  · exact S.connectionEntry_eq_zero_of_inner_band h g l T hμ hν hx hh hg hb
  by_cases hp : k % 2 ≠ j % 2
  · exact S.connectionEntry_eq_zero_of_inner_parity h g l T hμ hν hx hh hg hgpar hp
  have hkj : k=j+2*((k-j)/2) := by omega
  have hr : (k-j)/2 ≤ l := by omega
  by_cases ho : n < m ∨ m+h.natDegree+2*l < n
  · exact S.connectionEntry_eq_zero_of_outer_band h g l T hμ hν hx hh hg hk hj hkj hr ho
  exfalso
  apply hout
  exact ⟨n-m,(k-j)/2,by omega,hr,by omega,hkj⟩

/-- A separated even modification has an exact finite rectangle of allowed offsets. -/
theorem connectionEntry_eq_zero_of_outside_rectangle [μ.IsNegInvariant] [ν.IsNegInvariant]
    (hpos : Polynomial.HasPositiveDefiniteIntegral μ) (hh0 : h ≠ 0)
    (hhpar : ∀ x, h.eval (-x) = h.eval x) (hgpar : ∀ x, g.eval (-x) = g.eval x)
    (a : ℕ) (hhdeg : h.natDegree ≤ 2*a) (hgdeg : g.natDegree ≤ 2*l)
    {n k m j : ℕ} (hk : k ≤ n) (hj : j ≤ m)
    (hout : ¬ ∃ s r : ℕ, s ≤ a+l ∧ r ≤ l ∧ n=m+2*s ∧ k=j+2*r) :
    S.connectionEntry T n k m j = 0 := by
  by_cases hb : k < j ∨ j+g.natDegree < k
  · exact S.connectionEntry_eq_zero_of_inner_band h g l T hμ hν hx hh hg hb
  by_cases hp : k % 2 ≠ j % 2
  · exact S.connectionEntry_eq_zero_of_inner_parity h g l T hμ hν hx hh hg hgpar hp
  have hkj : k=j+2*((k-j)/2) := by omega
  have hr : (k-j)/2 ≤ l := by omega
  by_cases ho : n < m ∨ m+h.natDegree+2*l < n
  · exact S.connectionEntry_eq_zero_of_outer_band h g l T hμ hν hx hh hg hk hj hkj hr ho
  by_cases hp' : n % 2 ≠ m % 2
  · exact S.connectionEntry_eq_zero_of_total_parity h g l T hμ hν hx hh hg
      hpos hh0 hhpar hk hj hkj hp'
  exfalso
  apply hout
  exact ⟨(n-m)/2,(k-j)/2,by omega,hr,by omega,hkj⟩

/-- The same-index coefficient is positive in the positive-leading normalization. -/
theorem connectionEntry_diag_pos (n k : ℕ) : 0 < S.connectionEntry T n k n k := by
  let := (hμ.diskOuterModification hx h hh l).isFiniteMeasure
  let := (hν.polynomialDensityMeasure g hg).isFiniteMeasure
  dsimp only [connectionEntry, polynomial]
  rw [
    integralInner_cartesianDiskPolynomial_same_degree (ae_mem_diskOuterModification hx h l)
      _ _ _ _ k (by simp) (by simp) (S.inner_parity k) (T.inner_parity k)]
  apply mul_pos
  · exact (T.outer_orthogonal_real k).integralInner_pos_of_leadingCoeff_pos
      ((hμ.diskOuterModification hx h hh l).diskOuterMeasure
        (ae_mem_diskOuterModification hx h l) k)
      (S.outer k |>.natDegree_eq _) (S.outer_leadingCoeff_pos k (n-k))
      (T.outer_leadingCoeff_pos k (n-k))
      (by rw [Polynomial.integralInner_self,T.outer_norm_real]; exact zero_lt_one)
  · exact T.inner_orthogonal.integralInner_pos_of_leadingCoeff_pos
      (hν.polynomialDensityMeasure g hg) (S.inner.natDegree_eq k)
      (S.inner_leadingCoeff_pos k) (T.inner_leadingCoeff_pos k)
      (by rw [Polynomial.integralInner_self,T.inner_norm]; exact zero_lt_one)

end MvPolynomial.CartesianDiskSystem
