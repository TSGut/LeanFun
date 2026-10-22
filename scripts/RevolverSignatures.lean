import Lean

/-!
Signatures for the LeanFun RevOLVER.

Reads declaration names (one per line) on standard input and prints a JSON array
with, for each name, its kind, its elaborated signature as pretty-printed by Lean
(so every binder, including section variables and instances, is shown exactly as
the kernel sees it), and its defining module and source line range.
-/

open Lean

namespace RevolverSignatures

def resolveName (env : Environment) (s : String) : Option Name :=
  if env.contains s.toName then some s.toName
  else env.constants.toList.findSome? fun (n, _) => if n.toString == s then some n else none

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quotient"

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let input ← (← IO.getStdin).readToEnd
  let names := input.splitOn "\n" |>.map (·.replace "\r" "" |>.replace " " "") |>.filter (! ·.isEmpty)
  enableInitializersExecution
  let env ← importModules #[{module := `LeanFun}] {} (loadExts := true)
  let opts : Options := {}
  let mut out : Array Json := #[]
  for s in names do
    let some n := resolveName env s | do
      out := out.push <| Json.mkObj [("name", toJson s), ("missing", toJson true)]
      continue
    let some c := env.find? n | do
      out := out.push <| Json.mkObj [("name", toJson s), ("missing", toJson true)]
      continue
    let modName := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.toString
      | none => ""
    let ((sig, ranges), _, _) ← (do
      let f ← PrettyPrinter.ppSignature n
      let r ← findDeclarationRanges? n
      pure (toString f.fmt, r) : MetaM (String × Option DeclarationRanges)).toIO
        {fileName := "revolver", fileMap := default, options := opts} {env := env}
    let (line, endLine) := match ranges with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    out := out.push <| Json.mkObj [("name", toJson s), ("kind", toJson (kind c)),
      ("signature", toJson sig), ("module", toJson modName),
      ("line", toJson line), ("endLine", toJson endLine)]
  IO.println (toJson out).compress
  return 0

end RevolverSignatures

unsafe def main (args : List String) : IO UInt32 := RevolverSignatures.main args
