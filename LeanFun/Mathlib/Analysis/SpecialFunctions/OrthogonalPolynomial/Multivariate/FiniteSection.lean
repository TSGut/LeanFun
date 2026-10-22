/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Exact padding for finite polynomial multiplication

A truncation that fixes degree-at-most-`N` polynomials cannot affect a sequence
of multiplications whose intermediate degrees stay at most `N`. The bound is
on total degree, not the number of coefficients. It therefore applies equally
to univariate and multivariate degree sections, with any ordering inside blocks.

Reference: Gutleb–Olver–Slevinsky, measure modifications, Section 2.
-/

public section
namespace MvPolynomial
variable {σ R : Type*} [CommSemiring R]

/-- With enough degree padding, repeated truncated multiplication agrees exactly
with full polynomial multiplication. No assertion is made without the padding. -/
theorem iterate_truncated_mul_eq_pow_mul (T : MvPolynomial σ R → MvPolynomial σ R)
    (N : ℕ) (hT : ∀ q, q.totalDegree ≤ N → T q = q)
    (u p : MvPolynomial σ R) (k : ℕ)
    (hbound : p.totalDegree + k * u.totalDegree ≤ N) :
    (fun q => T (u * q))^[k] p = u ^ k * p := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : p.totalDegree + k * u.totalDegree ≤ N := by
      rw [Nat.succ_mul] at hbound
      omega
    rw [Function.iterate_succ_apply', ih hk]
    have hd : (u * (u ^ k * p)).totalDegree ≤ N := by
      have h₁ := totalDegree_mul u (u ^ k * p)
      have h₂ := totalDegree_mul (u ^ k) p
      have h₃ := totalDegree_pow u k
      rw [Nat.succ_mul] at hbound
      omega
    rw [hT _ hd, pow_succ']
    exact (mul_assoc _ _ _).symm

end MvPolynomial
