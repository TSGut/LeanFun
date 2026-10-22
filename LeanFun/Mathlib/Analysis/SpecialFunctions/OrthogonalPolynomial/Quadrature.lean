/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import LeanFun.Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomial.Roots
public import LeanFun.Mathlib.LinearAlgebra.Lagrange

/-!
# Gaussian quadrature for general measures

Weights are integrals of Mathlib's Lagrange basis polynomials at the roots.
Exactness through degree `2 * n - 1` and positivity use the existing moment
and positive-definiteness hypotheses, with no restriction on support.
Reference: DLMF §3.5(v), https://dlmf.nist.gov/3.5#v.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace Lagrange

variable {ι : Type*} [DecidableEq ι]

/-- Local domain for a classical quadrature integral (DLMF §3.5(iv)). -/
structure QuadratureInput (μ : Measure ℝ) (s : Finset ι) (v : ι → ℝ) (i : ι) where
  basis : BasisInput s v i
  integrable : Integrable (fun x ↦ (classicalBasis s v i basis).eval x) μ

/-- Finite moments supply the local integral domain. -/
abbrev QuadratureInput.ofMoments {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    {s : Finset ι} {v : ι → ℝ} {i : ι} (d : BasisInput s v i) :
    QuadratureInput μ s v i :=
  ⟨d, by simpa using hμ.integrable_mul (classicalBasis s v i d) 1⟩

/-- The bundled quadrature polynomial has a finite classical integral. -/
theorem QuadratureInput.integrable_eval {μ : Measure ℝ} {s : Finset ι}
    {v : ι → ℝ} {i : ι} (d : QuadratureInput μ s v i) :
    Integrable (fun x ↦ (classicalBasis s v i d.basis).eval x) μ := d.integrable

/-- The interpolatory quadrature weight on its classical domain (DLMF §3.5(iv)). -/
noncomputable def quadratureWeight (μ : Measure ℝ) (s : Finset ι) (v : ι → ℝ)
    (i : ι) (d : QuadratureInput μ s v i) : ℝ :=
  ∫ x, (classicalBasis s v i d.basis).eval x ∂μ

/-- Classical quadrature-weight integral formula. -/
theorem quadratureWeight_apply (μ : Measure ℝ) (s : Finset ι) (v : ι → ℝ)
    (i : ι) (d : QuadratureInput μ s v i) :
    quadratureWeight μ s v i d = ∫ x, (classicalBasis s v i d.basis).eval x ∂μ := rfl

/-- Integrating the Lagrange interpolant gives an exact rule below the node count
(DLMF §3.5(iv)). -/
theorem integral_eq_sum_quadratureWeight_mul_eval {μ : Measure ℝ}
    (hμ : HasFiniteMoments μ) {s : Finset ι} {v : ι → ℝ} (hv : Set.InjOn v s)
    {p : ℝ[X]} (hp : p.degree < s.card) :
    ∫ x, p.eval x ∂μ = ∑ i : s,
      quadratureWeight μ s v i (QuadratureInput.ofMoments hμ (BasisInput.of_injOn hv i.property)) *
        p.eval (v i) := by
  classical
  have hi (q : ℝ[X]) : Integrable (fun x ↦ q.eval x) μ := by
    simpa using hμ.integrable_mul q 1
  calc
    _ = ∫ x, ∑ i : s, p.eval (v i) *
        (classicalBasis s v i (BasisInput.of_injOn hv i.property)).eval x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      conv_lhs => rw [eq_sum_classicalBasis hv hp]
      simp only [eval_finsetSum, eval_mul, eval_C]
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ (hi _).const_mul _)]
      simp only [integral_const_mul, quadratureWeight, mul_comm]

end Lagrange

namespace Polynomial.Sequence

variable (P : Sequence ℝ)

/-- Gaussian weight at a real root of `P n`, without choosing an ordering of the roots
(DLMF §3.5(v)). -/
noncomputable def gaussWeight (μ : Measure ℝ) (n : ℕ) (x : ℝ)
    (d : Lagrange.QuadratureInput μ (P n).roots.toFinset id x) : ℝ :=
  Lagrange.quadratureWeight μ (P n).roots.toFinset id x d

/-- Gaussian weights are classical normalized-nodal-product integrals. -/
theorem gaussWeight_apply (μ : Measure ℝ) (n : ℕ) (x : ℝ)
    (d : Lagrange.QuadratureInput μ (P n).roots.toFinset id x) :
    P.gaussWeight μ n x d =
      ∫ y, (Lagrange.classicalBasis (P n).roots.toFinset id x d.basis).eval y ∂μ := rfl

variable {P} {μ : Measure ℝ} (hμ : HasFiniteMoments μ)
    (hpos : HasPositiveDefiniteIntegral μ) (hP : P.IsOrthogonal μ)

include hμ hpos hP

/-- There are exactly `n` distinct Gaussian nodes (DLMF §3.5(v)). -/
theorem IsOrthogonal.card_gaussNodes (n : ℕ) : (P n).roots.toFinset.card = n := by
  rw [Multiset.toFinset_card_of_nodup (hP.roots_nodup hμ hpos n), hP.card_roots hμ hpos]

/-- Gaussian quadrature is exact for every polynomial of degree strictly below `2*n`
(DLMF §3.5(v)). -/
theorem IsOrthogonal.integral_eq_sum_gaussWeight_mul_eval {n : ℕ} {p : ℝ[X]}
    (hp : p.degree < (2 * n : ℕ)) :
    ∫ x, p.eval x ∂μ = ∑ x ∈ (P n).roots.toFinset, P.gaussWeight μ n x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) * p.eval x := by
  classical
  have hi (q : ℝ[X]) : Integrable (fun x ↦ q.eval x) μ := by
    simpa using hμ.integrable_mul q 1
  have hqd : (p / P n).degree < n := by
    by_cases hq : p / P n = 0
    · simp [hq]
    have hp0 : p ≠ 0 := by intro hz; simp [hz] at hq
    have hge : (P n).degree ≤ p.degree := by
      exact le_of_not_gt (fun h ↦ hq ((Polynomial.div_eq_zero_iff (P.ne_zero n)).mpr h))
    have hd := degree_add_div (P.ne_zero n) hge
    rw [P.degree_eq, degree_eq_natDegree hq, degree_eq_natDegree hp0] at hd
    have hd' : n + (p / P n).natDegree = p.natDegree := by exact_mod_cast hd
    rw [degree_eq_natDegree hp0] at hp
    have hp' : p.natDegree < 2 * n := by exact_mod_cast hp
    rw [degree_eq_natDegree hq]
    exact_mod_cast (show (p / P n).natDegree < n by omega)
  have hzero := hP.integralInner_eq_zero_of_degree_lt hμ hqd
  have hrd : (p % P n).degree < (P n).roots.toFinset.card := by
    rw [hP.card_gaussNodes hμ hpos, ← P.degree_eq]
    exact degree_mod_lt _ (P.ne_zero n)
  have hrem := Lagrange.integral_eq_sum_quadratureWeight_mul_eval hμ
    (s := (P n).roots.toFinset) (v := id) (fun _ _ _ _ h ↦ h) hrd
  have he (x : ℝ) : p.eval x =
      (p / P n).eval x * (P n).eval x + (p % P n).eval x := by
    have h := congrArg (fun q : ℝ[X] ↦ q.eval x) (EuclideanDomain.div_add_mod p (P n))
    simpa [eval_add, eval_mul, mul_comm] using h.symm
  calc
    _ = ∫ x, (p % P n).eval x ∂μ := by
      simp_rw [he]
      rw [integral_add (hμ.integrable_mul _ _) (hi _)]
      change integralInner μ (IntegrablePair.of μ (p / P n) (P n)) + _ = _
      rw [hzero, zero_add]
    _ = _ := by
      rw [hrem]
      simp only [Lagrange.quadratureWeight, Lagrange.classicalBasis]
      rw [Finset.sum_coe_sort (P n).roots.toFinset (fun x ↦
        (∫ y, (Lagrange.basis (P n).roots.toFinset id x).eval y ∂μ) *
          (p % P n).eval (id x))]
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 : (P n).eval x = 0 :=
        (mem_roots (P.ne_zero n)).mp (Multiset.mem_toFinset.mp hx)
      have hxrem : (p % P n).eval x = p.eval x := by simpa [hx0] using (he x).symm
      simp [gaussWeight, Lagrange.quadratureWeight, Lagrange.classicalBasis, hxrem]

/-- A Gaussian weight equals the integral of the square of its Lagrange polynomial
(DLMF §3.5(v)). -/
theorem IsOrthogonal.gaussWeight_eq_integral_sq {n : ℕ} {x : ℝ}
    (hx : x ∈ (P n).roots.toFinset) :
    P.gaussWeight μ n x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) =
      ∫ y, (Lagrange.classicalBasis (P n).roots.toFinset id x (Lagrange.BasisInput.id _ _)).eval y ^ 2 ∂μ := by
  classical
  let l := Lagrange.basis (P n).roots.toFinset id x
  have hinj : Set.InjOn (id : ℝ → ℝ) (P n).roots.toFinset := fun _ _ _ _ h ↦ h
  have hn : 0 < n := by
    rw [← hP.card_gaussNodes hμ hpos n]
    exact Finset.card_pos.mpr ⟨x, hx⟩
  have hl : l ≠ 0 := Lagrange.basis_ne_zero hinj hx
  have hd : (l ^ 2).degree < (2 * n : ℕ) := by
    rw [degree_eq_natDegree (pow_ne_zero _ hl), natDegree_pow]
    have hld : l.natDegree = n - 1 := by
      simpa [l, hP.card_gaussNodes hμ hpos] using Lagrange.natDegree_basis hinj hx
    rw [hld]
    exact_mod_cast (show 2 * (n - 1) < 2 * n by omega)
  have he := hP.integral_eq_sum_gaussWeight_mul_eval hμ hpos hd
  simp only [eval_pow] at he
  change _ = ∫ y, l.eval y ^ 2 ∂μ
  rw [he]
  symm
  rw [Finset.sum_eq_single_of_mem x hx]
  · have hlx : l.eval x = 1 := Lagrange.eval_basis_self hinj hx
    simp only [hlx, one_pow, mul_one]
  · intro y hy hyx
    have hly : l.eval y = 0 := Lagrange.eval_basis_of_ne (v := id) hyx.symm hy
    simp only [hly, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]

/-- Every Gaussian weight is strictly positive (DLMF §3.5(v)). -/
theorem IsOrthogonal.gaussWeight_pos {n : ℕ} {x : ℝ}
    (hx : x ∈ (P n).roots.toFinset) : 0 < P.gaussWeight μ n x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) := by
  rw [hP.gaussWeight_eq_integral_sq hμ hpos hx]
  exact hpos _ (Lagrange.basis_ne_zero (fun _ _ _ _ h ↦ h) hx)

/-- Gaussian weights sum to the mass of the measure (DLMF §3.5(v)). -/
theorem IsOrthogonal.sum_gaussWeight {n : ℕ} (hn : 1 ≤ n) :
    ∑ x ∈ (P n).roots.toFinset, P.gaussWeight μ n x (Lagrange.QuadratureInput.ofMoments hμ (Lagrange.BasisInput.id _ _)) = μ.real Set.univ := by
  have hd : (1 : ℝ[X]).degree < (2 * n : ℕ) := by
    rw [degree_one]
    exact_mod_cast (show 0 < 2 * n by omega)
  have he := hP.integral_eq_sum_gaussWeight_mul_eval hμ hpos hd
  simpa using he.symm

end Polynomial.Sequence
