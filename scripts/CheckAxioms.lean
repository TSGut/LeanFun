import LeanFun
open Lean Elab Command

/-! Axiom audit for CI: `lake env lean scripts/CheckAxioms.lean`.
Every declaration from a `LeanFun` module may depend only on Lean's standard axioms.
This rejects `sorry` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`) and new axioms.
Declarations are selected by module, since LeanFun uses Mathlib namespaces. -/

elab "#check_leanfun_axioms" : command => do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut bad : Array MessageData := #[]
  for (c, _) in env.constants.toList do
    let some i := env.getModuleIdxFor? c | continue
    unless (`LeanFun).isPrefixOf env.header.moduleNames[i.toNat]! do continue
    checked := checked + 1
    let extra := (← liftCoreM (collectAxioms c)).filter (!standard.contains ·)
    unless extra.isEmpty do bad := bad.push m!"{c}: {extra.toList}"
  if bad.isEmpty then
    logInfo m!"checked {checked} LeanFun declarations: standard axioms only"
  else
    logError m!"{bad.size} LeanFun declarations use nonstandard axioms:\n{MessageData.joinSep bad.toList "\n"}"

#check_leanfun_axioms
