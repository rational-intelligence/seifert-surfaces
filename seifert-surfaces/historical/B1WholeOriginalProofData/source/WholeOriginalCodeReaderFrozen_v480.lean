import OriginalB1_v468
import B1ActualNativePositive_v468
import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 100000
partial def encodeStruct (e : Expr) : StateM (Std.HashMap ExprStructEq Nat × Array Json) Nat := do
  if let some n := (← get).1[ExprStructEq.mk e]? then return n
  let entry ← match e with
    | .bvar i => pure <| toJson ("bvar",i)
    | .fvar n => pure <| toJson ("fvar",n.name.toString)
    | .mvar n => pure <| toJson ("mvar",n.name.toString)
    | .sort l => pure <| toJson ("sort",reprStr l)
    | .const n ls => pure <| toJson ("const",n.toString,ls.map reprStr)
    | .app f a => pure <| toJson ("app",← encodeStruct f,← encodeStruct a)
    | .lam n t b bi => pure <| toJson ("lam",n.toString,← encodeStruct t,← encodeStruct b,reprStr bi)
    | .forallE n t b bi => pure <| toJson ("forall",n.toString,← encodeStruct t,← encodeStruct b,reprStr bi)
    | .letE n t v b nd => pure <| toJson ("let",n.toString,← encodeStruct t,← encodeStruct v,← encodeStruct b,nd)
    | .lit l => pure <| toJson ("lit",reprStr l)
    | .mdata d b => pure <| toJson ("mdata",reprStr d,← encodeStruct b)
    | .proj n i b => pure <| toJson ("proj",n.toString,i,← encodeStruct b)
  let (cache,ns) ← get
  set (cache.insert (ExprStructEq.mk e) ns.size,ns.push entry)
  return ns.size

def structJson (e : Expr) : Json :=
  let (r,(_,ns)) := (encodeStruct e).run ({},#[])
  Json.mkObj [("root",toJson r),("nodes",toJson ns)]

def constKind : ConstantInfo → String
  | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quotient"

def primitiveMeta : ConstantInfo → Json
  | .defnInfo d => toJson (d.all.map Name.toString,reprStr d.safety,
      match d.hints with | .opaque => "opaque" | .abbrev => "abbrev" | .regular n => "regular:" ++ toString n)
  | .opaqueInfo d => toJson (d.all.map Name.toString,d.isUnsafe)
  | .thmInfo d => toJson (d.all.map Name.toString)
  | .axiomInfo d => toJson d.isUnsafe
  | .inductInfo d => toJson (d.numParams,d.numIndices,d.all.map Name.toString,d.ctors.map Name.toString,
      d.numNested,d.isRec,d.isUnsafe,d.isReflexive)
  | .ctorInfo d => toJson (d.induct.toString,d.cidx,d.numParams,d.numFields,d.isUnsafe)
  | .recInfo d => toJson (d.all.map Name.toString,d.numParams,d.numIndices,d.numMotives,d.numMinors,d.k,d.isUnsafe,
      d.rules.map fun r => (r.ctor.toString,r.nfields))
  | .quotInfo d => toJson (match d.kind with | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind")

def owner (env : Environment) (n : Name) : String :=
  ((env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i]!.toString).getD "<current>"

def structureMetadata (env : Environment) (n : Name) : Json := Id.run do
  let some info := getStructureInfo? env n | return Json.null
  return Json.mkObj [
    ("ordered_field_names", toJson (info.fieldNames.map Name.toString)),
    ("fields", toJson (info.fieldInfo.map fun f =>
      (f.fieldName.toString, f.projFn.toString, reprStr f.binderInfo, f.subobject?.map Name.toString))),
    ("parents", toJson (info.parentInfo.map fun p =>
      (p.structName.toString, p.projFn.toString, p.subobject)))]

def sameRules (a b : ConstantInfo) : Bool :=
  match a,b with
  | .recInfo x,.recInfo y => x.rules.length == y.rules.length &&
      (x.rules.zip y.rules).all (fun (r,s) => r.ctor == s.ctor && r.nfields == s.nfields && Expr.equal r.rhs s.rhs && ExprStructEq.mk r.rhs == ExprStructEq.mk s.rhs)
  | .recInfo _,_ => false
  | _,.recInfo _ => false
  | _,_ => true

def rulesJson (ci : ConstantInfo) : Json :=
  match ci with
  | .recInfo d => toJson (d.rules.map fun r => Json.mkObj [("constructor",toJson r.ctor.toString),
      ("fields",toJson r.nfields),("rhs",structJson r.rhs)])
  | _ => toJson ([] : List Json)

def sameNativeMetadata (a b : ConstantInfo) : Bool :=
  a.name == b.name && match a, b with
  | .defnInfo x, .defnInfo y => x.all == y.all && x.safety == y.safety &&
      (match x.hints, y.hints with
        | .opaque, .opaque => true | .abbrev, .abbrev => true
        | .regular i, .regular j => i == j | _, _ => false)
  | .opaqueInfo x, .opaqueInfo y => x.all == y.all && x.isUnsafe == y.isUnsafe
  | .thmInfo x, .thmInfo y => x.all == y.all
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | .inductInfo x, .inductInfo y => x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.all == y.all && x.ctors == y.ctors && x.numNested == y.numNested &&
      x.isRec == y.isRec && x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .ctorInfo x, .ctorInfo y => x.induct == y.induct && x.cidx == y.cidx &&
      x.numParams == y.numParams && x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
  | .recInfo x, .recInfo y => x.all == y.all && x.numParams == y.numParams &&
      x.numIndices == y.numIndices && x.numMotives == y.numMotives &&
      x.numMinors == y.numMinors && x.k == y.k && x.isUnsafe == y.isUnsafe && sameRules a b
  | .quotInfo x, .quotInfo y =>
      (match x.kind, y.kind with
        | .type, .type => true | .ctor, .ctor => true
        | .lift, .lift => true | .ind, .ind => true | _, _ => false)
  | _, _ => false

def nameIndex (env : Environment) : Std.HashMap String (Name × ConstantInfo) := Id.run do
  let mut result : Std.HashMap String (Name × ConstantInfo) := {}
  for data in env.header.moduleData do
    for n in data.constNames do
      if let some ci := env.find? n then result := result.insert n.toString (n, ci)
  return result


set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array Name := #[`SeifertSurfaces.OriginalEndpoints.B1_original,
    `SeifertSurfaces.OriginalEndpoints.original_prop57_tangencies]
  let directory := System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/WHOLE_ORIGINAL_RELEASE_v480/reader"
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  let mut modules : NameSet := {}
  let mut leaves : NameSet := {}
  let mut textRows : Array String := #[]
  let mut i := 0
  while i < todo.size do
    let n := todo[i]!; i := i + 1
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "reader dependency absent {n}"
    let some mid := env.getModuleIdxFor? n | leaves := leaves.insert n; continue
    let module := env.header.moduleNames[mid]!
    let path ← liftIO <| findOLean module
    if path.toString.startsWith "/home/caoyichuan/.elan/" || path.toString.contains ".lake/packages/" then
      leaves := leaves.insert n
      continue
    modules := modules.insert module
    let mut deps := ci.type.getUsedConstants
    let body : Option Expr := match ci with
      | .defnInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    if let some v := body then deps := deps ++ v.getUsedConstants
    match ci with
    | .inductInfo v => deps := deps ++ v.all.toArray ++ v.ctors.toArray
    | .ctorInfo v => deps := deps.push v.induct
    | .recInfo v =>
      deps := deps ++ v.all.toArray
      for r in v.rules do deps := deps ++ r.rhs.getUsedConstants |>.push r.ctor
    | _ => pure ()
    todo := todo ++ deps
    let typeText ← liftTermElabM <| ppExpr ci.type
    let bodyText ← match body with
      | some v => liftTermElabM <| ppExpr v
      | none => pure Format.nil
    let universeCode := String.intercalate ", " (ci.levelParams.map Name.toString)
    let declarationText := constKind ci ++ " " ++ n.toString ++ ".{" ++ universeCode ++ "} :\n" ++ typeText.pretty 100 ++ "\n" ++
      (if body.isSome then s!":=\n{bodyText.pretty 100}\n" else "")
    textRows := textRows.push declarationText
    rows := rows.push <| Json.mkObj [("name",toJson n.toString),("kind",toJson (constKind ci)),
      ("module",toJson module.toString),("object",toJson path.toString),
      ("ordered_universes",toJson (ci.levelParams.map Name.toString)),
      ("type_expr",structJson ci.type),("type_code",toJson typeText.pretty),
      ("definition_expr",body.map structJson |>.getD Json.null),
      ("definition_code",if body.isSome then toJson bodyText.pretty else Json.null),
      ("primitive_metadata",primitiveMeta ci),("structure_metadata",structureMetadata env n),
      ("recursor_rules",rulesJson ci)]
  liftIO <| IO.FS.writeFile (directory / "OPERATIVE_CUSTOM_DECLARATIONS_v480.json") <|
    (Json.mkObj [("roots",toJson (roots.map Name.toString)),("declarations",Json.arr rows),
      ("standard_library_leaves",toJson (leaves.toArray.map Name.toString)),
      ("module_names",toJson (modules.toArray.map Name.toString))]).pretty
  liftIO <| IO.FS.writeFile (directory / "OPERATIVE_CUSTOM_CODE_v480.txt") <|
    String.intercalate "\n" textRows.toList
  logInfo m!"Code-only reader packet: {rows.size} custom declarations; {modules.toArray.size} operative modules; {leaves.toArray.size} standard leaves"
