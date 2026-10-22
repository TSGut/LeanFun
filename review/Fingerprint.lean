import Lean

open Lean

namespace Review

def tag (s : String) (xs : List Json := []) : Json := toJson (Json.str s :: xs)

def nameJson : Name → Json
  | .anonymous => tag "anonymous"
  | .str p s => tag "str" [nameJson p, toJson s]
  | .num p n => tag "num" [nameJson p, toJson n]

-- Printed dependency names can contain numeric or escaped components; do not
-- reconstruct them by merely splitting at dots.
def resolveName (env : Environment) (s : String) : Option Name :=
  if env.contains s.toName then some s.toName
  else env.constants.toList.findSome? fun (n, _) => if n.toString == s then some n else none

def binder : BinderInfo → String
  | .default => "explicit" | .implicit => "implicit"
  | .strictImplicit => "strictImplicit" | .instImplicit => "instance"

partial def level (ps : List Name) : Level → Except String Json
  | .zero => pure (tag "zero")
  | .succ l => return tag "succ" [← level ps l]
  | .max a b => return tag "max" [← level ps a, ← level ps b]
  | .imax a b => return tag "imax" [← level ps a, ← level ps b]
  | .param n => match ps.idxOf? n with
    | some i => pure (tag "param" [toJson i])
    | none => .error s!"Unknown universe parameter {n}"
  | .mvar _ => .error "Unresolved universe metavariable"

partial def expr (ps : List Name) : Expr → Except String Json
  | .bvar i => pure (tag "bvar" [toJson i])
  | .fvar _ => .error "Unexpected free variable"
  | .mvar _ => .error "Unexpected metavariable"
  | .sort l => return tag "sort" [← level ps l]
  | .const n ls => return tag "const" [nameJson n, toJson (← ls.mapM (level ps))]
  | .app f a => return tag "app" [← expr ps f, ← expr ps a]
  | .lam _ t b bi => return tag "lam" [toJson (binder bi), ← expr ps t, ← expr ps b]
  | .forallE _ t b bi => return tag "forall" [toJson (binder bi), ← expr ps t, ← expr ps b]
  | .letE _ t v b nondep => return tag "let" [toJson nondep, ← expr ps t, ← expr ps v, ← expr ps b]
  | .lit (.natVal n) => pure (tag "nat" [toJson n])
  | .lit (.strVal s) => pure (tag "string" [toJson s])
  | .mdata _ e => expr ps e
  | .proj n i e => return tag "proj" [nameJson n, toJson i, ← expr ps e]

partial def refs (e : Expr) : List Name :=
  match e with
  | .const n _ => [n]
  | .app a b | .lam _ a b _ | .forallE _ a b _ => refs a ++ refs b
  | .letE _ a b c _ => refs a ++ refs b ++ refs c
  | .mdata _ a => refs a
  | .proj n _ a => n :: refs a
  | _ => []

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quotient"

def expressions (c : ConstantInfo) : List Expr :=
  c.type :: (match c with
    | .defnInfo v => [v.value]
    | .opaqueInfo v => [v.value]
    | _ => [])

def links : ConstantInfo → List Name
  | .inductInfo v => v.all ++ v.ctors
  | .ctorInfo v => [v.induct]
  | .recInfo v => v.all
  | _ => []

def localDecl (env : Environment) (n : Name) (modulePrefix : String) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some i => let m := env.header.moduleNames[i.toNat]!.toString
              m == modulePrefix || m.startsWith (modulePrefix ++ ".")

partial def collect (env : Environment) (modulePrefix : String) (todo seen : List Name)
    (records : Array Json) (external : List String) : Except String (Array Json × List String) := do
  match todo with
  | [] => return (records, external)
  | n :: todo =>
    if seen.contains n then return ← collect env modulePrefix todo seen records external
    let some c := env.find? n | throw s!"Missing constant: {n}"
    let es := expressions c
    let extra := links c
    let record := Json.mkObj [("name", toJson n.toString), ("id", nameJson n), ("kind", toJson (kind c)),
      ("universes", toJson c.levelParams.length),
      ("expressions", toJson (← es.mapM (expr c.levelParams))),
      ("links", toJson (extra.map nameJson))]
    let mut next := todo
    let mut ext := external
    for dep in es.flatMap refs ++ extra do
      unless env.contains dep do throw s!"Missing constant: {dep}"
      if localDecl env dep modulePrefix then next := dep :: next
      else ext := dep.toString :: ext
    collect env modulePrefix next (n :: seen) (records.push record) ext

unsafe def mainImpl (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut names := args
  let mut mod := `LeanFun
  let mut modulePrefix := "LeanFun"
  if names.head? == some "--module" then
    if names.length < 4 then throw (IO.userError "--module MODULE PREFIX DECL...")
    mod := names[1]!.toName
    modulePrefix := names[2]!
    names := names.drop 3
  let externalNames := (names.dropWhile (· != "--check-external")).drop 1
  names := names.takeWhile (· != "--check-external")
  if names.isEmpty then
    let out ← IO.Process.output {cmd := "python3", args := #["scripts/review.py", "names"]}
    unless out.exitCode == 0 do throw (IO.userError out.stderr)
    names := out.stdout.splitOn "\n" |>.filter (! ·.isEmpty)
  -- `lake exe` builds this executable, not its dynamically imported project.
  -- Fixture imports are built explicitly by the test harness.
  if mod == `LeanFun then
    let build ← IO.Process.output {cmd := "lake", args := #["build", "LeanFun"]}
    IO.eprint build.stdout
    IO.eprint build.stderr
    unless build.exitCode == 0 do return build.exitCode
  enableInitializersExecution
  let env ← importModules #[{module := mod}] {} (loadExts := true)
  let missingExternal := externalNames.filter fun s => (resolveName env s).isNone
  let mut output : Array Json := #[]
  for s in names do
    let n := (resolveName env s).getD s.toName
    let some c := env.find? n | do
      output := output.push <| Json.mkObj [("name", toJson s), ("missing", toJson true)]
      continue
    let (records, external) ← IO.ofExcept (collect env modulePrefix [n] [] #[] [])
    -- Human display uses ordinary Lean notation. Fingerprints above retain all
    -- elaborated arguments, universes and local definition dependencies.
    let opts : Options := {}
    let (rendered, _, _) ← (do
      let t ← Meta.ppExpr c.type
      let mut result := s!"{kind c} {n} : {t}"
      for e in (expressions c).drop 1 do
        result := result ++ s!"\n:= {← Meta.ppExpr e}"
      for ln in links c do
        if let some lc := env.find? ln then
          result := result ++ s!"\n{ln} : {← Meta.ppExpr lc.type}"
      pure result : MetaM String).toIO
        {fileName := "review", fileMap := default, options := opts} {env := env}
    output := output.push <| Json.mkObj [("name", toJson s), ("kind", toJson (kind c)),
      ("rendered", toJson rendered), ("records", toJson records),
      ("missing_external", toJson missingExternal),
      ("external", toJson external)]
  let result ← IO.Process.output {cmd := "python3", args := #["scripts/review_hash.py"]}
    (some (toJson output).compress)
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode

end Review

unsafe def main (args : List String) : IO UInt32 := Review.mainImpl args
