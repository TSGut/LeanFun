/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Mathlib.Data.Matrix.Basic

/-! # Banded matrices with natural indices
Rows are output indices and columns are input indices. The lower and upper
bandwidths are recorded separately. Reference: Olver--Townsend (2013).
-/

@[expose] public section
namespace Matrix
variable {R : Type*} [Zero R]

/-- Entries vanish below the `lower`th subdiagonal and above the `upper`th
superdiagonal. This definition does not require finite index sets or matrix
multiplication. Reference: Olver--Townsend (2013), §2. -/
def IsBanded (A : Matrix ℕ ℕ R) (lower upper : ℕ) : Prop :=
  ∀ i j, j + lower < i ∨ i + upper < j → A i j = 0

/-- Increasing either bandwidth preserves bandedness (Olver--Townsend 2013, §2). -/
theorem IsBanded.mono {A : Matrix ℕ ℕ R} {l u l' u' : ℕ}
    (h : A.IsBanded l u) (hl : l ≤ l') (hu : u ≤ u') : A.IsBanded l' u' := by
  intro i j hij
  apply h
  omega

end Matrix
