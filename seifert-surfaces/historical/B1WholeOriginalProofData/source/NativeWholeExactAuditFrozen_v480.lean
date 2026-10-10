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


run_cmd do
  let env := (← getEnv).setExporting false
  liftIO enableInitializersExecution
  let candidateSearchPath ← liftIO searchPathRef.get
  let .ok originalConfig := Json.parse (← liftIO <| IO.FS.readFile
    "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/build_environment.json") | throwError "original context config"
  let .ok originalLeanPath := originalConfig.getObjValAs? String "LEAN_PATH" | throwError "original LEAN_PATH"
  liftIO <| searchPathRef.set ((originalLeanPath.splitOn ":").map System.FilePath.mk)
  let baseline ← liftIO <| importModules #[{module := `VM03ExactCaller_v464},
    {module := `B1GlobalInverseMetric}, {module := `B1SimultaneousMetricMinimizer},
    {module := `B1GraphCoefficients}, {module := `B1TangencyGlobal}, {module := `B1NativeBoundaryChart_v466}, {module := `Lean}] {} 0 (loadExts := true)
  liftIO <| searchPathRef.set candidateSearchPath
  let baseline := baseline.setExporting false
  let preservedModules : Array Name := #[`B1ChartMetricProvider, `B1TangencyCoordinates,
    `B1TangencyPositive, `B1TangencyGraph, `B1GraphCoefficients,
    `B1MetricVariationalInterfaces, `B1GlobalInverseMetric, `B1SimultaneousMetricMinimizer,
    `OriginalB1, `B1SourceContext, `B1ActualGeometry, `B1TangencyReflection,
    `B1TangencyFiniteOrder, `B1TangencyGlobal, `B1BoundaryMetricProvider_v466, `B1NativeBoundaryChart_v466]
  let mut contracts : Nat := 0
  let mut values : Nat := 0
  let mut rules : Nat := 0
  let mut fields : Nat := 0
  let mut rows : Array Json := #[]
  for i in [:baseline.header.moduleNames.size] do
    let module := baseline.header.moduleNames[i]!
    if !preservedModules.contains module then continue
    let mut count : Nat := 0
    for n in baseline.header.moduleData[i]!.constNames do
      let some a := baseline.find? n | throwError "baseline missing {n}"
      let some b := env.find? n | throwError "candidate missing sibling {n}"
      unless owner baseline n == owner env n && a.levelParams == b.levelParams &&
          Expr.equal a.type b.type && ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
          sameNativeMetadata a b && structureMetadata baseline n == structureMetadata env n do
        throwError "sibling raw contract metadata drift {n}; old owner {owner baseline n}; new owner {owner env n}; literal type equal {ExprStructEq.mk a.type == ExprStructEq.mk b.type}; metadata equal {sameNativeMetadata a b}"
      match a.value? (allowOpaque := true), b.value? (allowOpaque := true) with
      | some av, some bv =>
        unless Expr.equal av bv && ExprStructEq.mk av == ExprStructEq.mk bv do
          throwError "sibling actual unsanitized value drift {n}"
        values := values + 1
      | none, none => pure ()
      | _, _ => throwError "sibling value availability drift {n}"
      if let .recInfo r := a then rules := rules + r.rules.length
      if let some st := getStructureInfo? baseline n then fields := fields + st.fieldInfo.size
      contracts := contracts + 1
      count := count + 1
    rows := rows.push <| Json.mkObj [("module",toJson module.toString),("heads",toJson count)]
  let .ok seedsJson := Json.parse (← liftIO <| IO.FS.readFile
    "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/inputs/NATIVE229_SEEDS_v468.json") | throwError "native229 seeds"
  let .ok seeds := fromJson? seedsJson (α := Array String) | throwError "native229 names"
  let prior := nameIndex baseline
  let current := nameIndex env
  let mut native229Values := 0
  for string in seeds do
    let some (n,a) := prior[string]? | throwError "current canonical seed absent {string}"
    let some (m,b) := current[string]? | throwError "candidate native seed absent {string}"
    unless n == m && a.levelParams == b.levelParams && owner baseline n == owner env m &&
        ExprStructEq.mk a.type == ExprStructEq.mk b.type && Expr.equal a.type b.type &&
        sameNativeMetadata a b && structureMetadata baseline n == structureMetadata env m do
      throwError "native229 current-canonical raw drift {string}"
    match a.value? (allowOpaque := true), b.value? (allowOpaque := true) with
    | some x, some y =>
      unless ExprStructEq.mk x == ExprStructEq.mk y && Expr.equal x y do
        throwError "native229 literal value drift {string}"
      native229Values := native229Values + 1
    | none, none => pure ()
    | _, _ => throwError "native229 value availability drift {string}"
  liftIO <| IO.FS.writeFile
    "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/WHOLE_ORIGINAL_RELEASE_v480/logs/NATIVE229_WHOLE_CURRENT_CANONICAL_PRESERVATION_FROZEN_v480.json"
    (Json.mkObj [("status",toJson "PASS"),("contracts",toJson seeds.size),
      ("literal_values",toJson native229Values),("proof_exceptions",toJson (0 : Nat)),
      ("baseline",toJson "exact current canonical VM03 + imported source providers"),
      ("historical_preimage_replayed",toJson false),("raw_ExprStructEq_AND_Expr_equal",toJson true)]).pretty
  let pairs : Array (Name × String) := #[
    (`SeifertSurfaces.OriginalEndpoints.original_prop57_tangencies, "B1geometry2_dde3e31a6d588db7"),
    (`SeifertSurfaces.OriginalEndpoints.B1_original, "originalB1fix_a95491d0e8f002b4")]
  let mut rootRows : Array Json := #[]
  for (root, task) in pairs do
    let some ci := env.find? root | throwError "root absent {root}"
    let .ok snap := Json.parse (← liftIO <| IO.FS.readFile
      ("/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/inputs/" ++ task ++ ".actual_unsanitized.json")) | throwError "snapshot parse"
    let (raw, typeKey, univKey) ← match snap.getObjVal? "actual_unerased_contract" with
      | .ok raw => pure (raw, "type_expr", "ordered_universes")
      | .error _ => do
        let .ok binding := snap.getObjVal? "actual_unsanitized_kernel_row" | throwError "native snapshot contract"
        let .ok raw := binding.getObjVal? "actual_unsanitized_row" | throwError "native snapshot row"
        pure (raw, "type", "universe_parameters")
    let .ok ty := raw.getObjVal? typeKey | throwError "snapshot type"
    let .ok univ := raw.getObjValAs? (Array String) univKey | throwError "universes"
    unless (ci.levelParams.map Name.toString).toArray == univ do throwError "ordered universe drift {root}"
    unless structJson ci.type == ty do throwError "full literal raw type drift {root}"
    let some proof := ci.value? (allowOpaque := true) | throwError "root proof absent {root}"
    liftTermElabM <| checkWithKernel proof
    rootRows := rootRows.push <| Json.mkObj [("root",toJson root.toString),
      ("task",toJson task),("snapshot_raw_type_literal_equal",toJson true),
      ("kernel_value_rechecked",toJson true),("actual_type_expr",structJson ci.type),
      ("actual_proof_expr",structJson proof),("actual_ordered_universes",toJson ci.levelParams)]
  let mut newHeads : Array Json := #[]
  for i in [:env.header.moduleNames.size] do
    let module := env.header.moduleNames[i]!
    if !module.toString.endsWith "_v468" && !module.toString.endsWith "_v474" && !module.toString.endsWith "_v475" then continue
    for n in env.header.moduleData[i]!.constNames do
      let ci := (env.find? n).get!
      newHeads := newHeads.push <| Json.mkObj [("name",toJson n.toString),
        ("kind",toJson (constKind ci)),("owner",toJson module.toString),
        ("type_expr",structJson ci.type),
        ("value_expr",ci.value? (allowOpaque := true) |>.map structJson |>.getD Json.null)]
  liftIO <| IO.FS.writeFile "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/WHOLE_ORIGINAL_RELEASE_v480/logs/NATIVE_EXACT_WHOLE_AUDIT_FROZEN_v480.json" <|
    (Json.mkObj [("status",toJson "PASS_LITERAL_RAW_TYPES_AND_ALL_CURRENT_SIBLING_VALUES"),
      ("preserved_contracts",toJson contracts),("preserved_values",toJson values),
      ("preserved_rules",toJson rules),("preserved_structure_fields",toJson fields),
      ("modules",toJson rows),("root_contracts",toJson rootRows),
      ("new_heads",toJson newHeads),("proof_exceptions_in_existing_modules",toJson (0 : Nat)),
      ("Expr_equal_AND_ExprStructEq",toJson true)]).pretty
  logInfo m!"Native exact audit PASS: {contracts} contracts; {values} values; full original roots 2"
