import OriginalB1_v468
import B1ActualGeometry_v468
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



run_cmd do
  let env := (← getEnv).setExporting false
  let candidateSearchPath ← liftIO searchPathRef.get
  let .ok cfg := Json.parse (← liftIO <| IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/build_environment.json") | throwError "original context config"
  let .ok oldPath := cfg.getObjValAs? String "LEAN_PATH" | throwError "original path"
  liftIO <| searchPathRef.set ((oldPath.splitOn ":").map System.FilePath.mk)
  liftIO enableInitializersExecution
  let original ← liftIO <| importModules #[{module:=`OriginalB1_v468},{module:=`Lean}] {} 0 (loadExts:=true)
  liftIO <| searchPathRef.set candidateSearchPath
  let original := original.setExporting false
  let mut rows : Array Json := #[]
  let mut aliases : Array Json := #[]
  let mut modules : Array Json := #[]
  let mut bad : Array String := #[]
  let mut values := 0
  let mut rules := 0
  for module in env.header.moduleNames do
    let path ← liftIO <| findOLean module
    if path.toString.contains "/.lake/packages/" || path.toString.startsWith "/home/caoyichuan/.elan/" then continue
    unless path.toString.startsWith "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/WHOLE_ORIGINAL_RELEASE_v480/objects/" do
      throwError "mutable project provider loaded {path}"
    let (md,_) ← liftIO <| readModuleData path
    for index in [:md.constants.size] do
      let a := md.constants[index]!
      let some b := env.find? a.name | throwError "loaded constant missing {a.name}"
      let te := Expr.equal a.type b.type && ExprStructEq.mk a.type == ExprStructEq.mk b.type
      let ve := match a.value? (allowOpaque:=true), b.value? (allowOpaque:=true) with
        | some av,some bv => Expr.equal av bv && ExprStructEq.mk av == ExprStructEq.mk bv
        | none,none => true | _,_ => false
      let me := sameNativeMetadata a b
      let re := sameRules a b
      let le := a.levelParams == b.levelParams
      let loadedOwner := owner env a.name
      let duplicate := loadedOwner != module.toString
      let originalOwner := owner original a.name
      let oldNativeOwnerRetained := originalOwner == loadedOwner
      let allEqual := te && ve && me && re && le
      if !(allEqual && (!duplicate || oldNativeOwnerRetained)) then bad := bad.push a.name.toString
      if (a.value? (allowOpaque:=true)).isSome then values := values + 1
      if let .recInfo r := a then rules := rules + r.rules.length
      let row := Json.mkObj [("name",toJson a.name.toString),("kind",toJson (constKind a)),
        ("saved_module",toJson module.toString),("saved_object",toJson path.toString),
        ("saved_constant_index",toJson index),("loaded_owner",toJson loadedOwner),
        ("original_v475_loaded_owner",toJson originalOwner),
        ("type_Expr_equal_AND_ExprStructEq",toJson te),("operative_value_Expr_equal_AND_ExprStructEq",toJson ve),
        ("metadata_equal",toJson me),("recursor_rules_equal",toJson re),("ordered_universes_equal",toJson le),
        ("structure_metadata",structureMetadata env a.name),
        ("equal_saved_alias",toJson duplicate),("original_loaded_owner_retained",toJson oldNativeOwnerRetained)]
      rows := rows.push row
      if duplicate then aliases := aliases.push row
    modules := modules.push <| Json.mkObj [("module",toJson module.toString),("object",toJson path.toString),
      ("constants",toJson md.constants.size),("imports",toJson (md.imports.map fun i=>i.module.toString))]
  let out := System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/WHOLE_ORIGINAL_RELEASE_v480/logs/FULL_RAW_PROVIDER_INVENTORY_v480.json"
  liftIO <| IO.FS.writeFile out <| (Json.mkObj [("okay",toJson bad.isEmpty),
    ("modules_count",toJson modules.size),("constant_rows",toJson rows.size),("operative_values",toJson values),
    ("recursor_rules",toJson rules),("bad",toJson bad),("rows",Json.arr rows),
    ("equal_alias_rows",Json.arr aliases),("modules",Json.arr modules),
    ("raw_expressions_pinned_in_original_opaque_module_objects",toJson true),
    ("normalization",toJson false),("proof_or_value_erasure",toJson false)]).pretty
  unless bad.isEmpty do throwError "frozen provider inventory rejected {bad}"
  logInfo m!"Full frozen provider inventory PASS: {modules.size} modules; {rows.size} rows; {aliases.size} literal equal aliases with unchanged original operative owner"
#print axioms SeifertSurfaces.OriginalEndpoints.B1_original
#print axioms SeifertSurfaces.OriginalEndpoints.original_prop57_tangencies
