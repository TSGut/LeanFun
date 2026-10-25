import Lean
open Lean

/-! Blueprint dependency extraction for `scripts/check_blueprint_graph.py`.
For each linked declaration, print the linked declarations its statement (and, for
definitions, its body) uses, following unlinked helpers. With a third argument,
theorem proofs are followed too. -/

/-- LeanFun-local constants mentioned by a statement type, or by a definition body
(theorem proofs are never followed), stopping at constants in `stop`. -/
def isLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some i => (env.header.moduleNames[i.toNat]!).toString.startsWith "LeanFun"

def exprs (c : ConstantInfo) : List Expr :=
  c.type :: (match c with
    | .defnInfo v => [v.value] | .opaqueInfo v => [v.value] | _ => [])

def proofExprs (c : ConstantInfo) : List Expr :=
  exprs c ++ (match c with | .thmInfo v => [v.value] | _ => [])

def direct (env : Environment) (n : Name) (withProofs := false) (linked : NameSet := {}) : Array Name := Id.run do
  let some c := env.find? n | return #[]
  let mut out : NameSet := {}
  -- A structure's fields live in its constructor type, not in the structure's own type.
  let ctors := match c with
    | .inductInfo v => v.ctors.filterMap fun k => (env.find? k).map (·.type)
    | _ => []
  for e in (if withProofs then proofExprs c else exprs c) ++ ctors do
    for d in e.getUsedConstants do
      if d != n && (isLocal env d || linked.contains d) then out := out.insert d
  return out.toArray

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- Only constant declarations and their module indices are inspected here.
  -- Tactic/attribute extensions are unnecessary and expensive to initialize.
  let env ← importModules #[{module := `LeanFun}] {} (loadExts := false)
  let names := (← IO.FS.readFile args[0]!).splitOn "\n" |>.filter (! ·.isEmpty)
  let linked : NameSet := names.foldl (fun s x => s.insert x.toName) {}
  -- For each linked declaration: the linked constants reached through unlinked helpers.
  let withProofs := args.length > 2
  let mut lines : Array String := #[]
  for s in names do
    let n := s.toName
    unless env.contains n do
      lines := lines.push (s ++ "\t!missing")
      continue
    let mut seen : NameSet := {}
    let mut todo := direct env n withProofs linked
    let mut hit : NameSet := {}
    while h : todo.size > 0 do
      let d := todo.back
      todo := todo.pop
      if seen.contains d then continue
      seen := seen.insert d
      if linked.contains d then hit := hit.insert d
      else todo := todo ++ direct env d withProofs linked
    lines := lines.push (s ++ "\t" ++ ",".intercalate (hit.toList.map toString))
  IO.FS.writeFile args[1]! ("\n".intercalate lines.toList ++ "\n")
