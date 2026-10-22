/-
Copyright (c) 2026 Timon S. Gutleb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Timon S. Gutleb
-/
module

public import Aesop

/-!
# Polynomial integrability proof rules

A dedicated rule set supplies the proof fields of integrable polynomial pairs.
These rules prove integrability; they never define an integral on a failed domain.
-/

declare_aesop_rule_sets [PolynomialIntegrability]
