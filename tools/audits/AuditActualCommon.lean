import Lean
import MainTheorems
import ExactPaidCodec
open Lean ExactPaidSource
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def exactExpr (e : Expr) : IO Json := do
 let j := exprJson e
 let a ← IO.ofExcept <| exprFromJson j
 unless Expr.equal a e && ExprStructEq.mk a == ExprStructEq.mk e do throw <| IO.userError "literal Expr codec roundtrip drift"
 return j
def metadata (ci : ConstantInfo) : Json :=
 let ns (xs : List Name) := toJson (xs.map nameJson)
 match ci with
 | .thmInfo v => Json.mkObj [("kind",toJson "theorem"),("all",ns v.all)]
 | .defnInfo v => Json.mkObj [("kind",toJson "definition"),("all",ns v.all),("hints",toJson (match v.hints with | .opaque => "opaque" | .abbrev => "abbrev" | .regular n => "regular " ++ toString n)),("safety",toJson (reprStr v.safety))]
 | .opaqueInfo v => Json.mkObj [("kind",toJson "opaque"),("all",ns v.all),("unsafe",toJson v.isUnsafe)]
 | .inductInfo v => Json.mkObj [("kind",toJson "inductive"),("all",ns v.all),("ctors",ns v.ctors),("numParams",toJson v.numParams),("numIndices",toJson v.numIndices),("numNested",toJson v.numNested),("isRec",toJson v.isRec),("unsafe",toJson v.isUnsafe),("isReflexive",toJson v.isReflexive)]
 | .ctorInfo v => Json.mkObj [("kind",toJson "constructor"),("induct",nameJson v.induct),("cidx",toJson v.cidx),("numParams",toJson v.numParams),("numFields",toJson v.numFields),("unsafe",toJson v.isUnsafe)]
 | .recInfo v => Json.mkObj [("kind",toJson "recursor"),("all",ns v.all),("numParams",toJson v.numParams),("numIndices",toJson v.numIndices),("numMotives",toJson v.numMotives),("numMinors",toJson v.numMinors),("k",toJson v.k),("unsafe",toJson v.isUnsafe)]
 | _ => Json.mkObj [("kind",toJson "FORBIDDEN")]

def readRows (p : System.FilePath) : IO (Array Json) := do
 let t ← IO.FS.readFile p
 return ← (t.splitOn "\n" |>.filter (· != "")).toArray.mapM (fun l => IO.ofExcept (Json.parse l))
def typedCheck (env : Environment) (ty va : Expr) := Kernel.check env {} (.letE `auditExactType ty va (.bvar 0) false)
def checkResult (r : Except Kernel.Exception Expr) : IO Json := do
 match r with
 | .ok _ => return toJson "PASS"
 | .error e => return Json.mkObj [("FAIL",toJson (← (e.toMessageData {}).toString))]
def defeqResult (env : Environment) (a b : Expr) : IO Json := do
 match Kernel.isDefEq env {} a b with
 | .ok true => return toJson "PASS"
 | .ok false => return toJson "FAIL"
 | .error e => return Json.mkObj [("FAIL",toJson (← (e.toMessageData {}).toString))]
def equalityResult (env : Environment) (ty a b : Expr) : IO Json := do
 match Kernel.check env {} ty with
 | .error e => checkResult (.error e)
 | .ok st => match Kernel.whnf env {} st with
  | .ok (.sort u) => checkResult <| typedCheck env (mkApp3 (mkConst `Eq [u]) ty a b) (mkApp2 (mkConst `Eq.refl [u]) ty a)
  | _ => return toJson "FAIL:type not sorted"
partial def remapFinite (maps : Std.HashMap Name Name) (e : Expr) : Expr := e.replace fun x => match x with
 | .const n ls => maps[n]?.map fun m => .const m ls
 | .proj n i b => maps[n]?.map fun m => .proj m i (remapFinite maps b)
 | _ => none
partial def remapJson (maps : Std.HashMap Name Name) (j : Json) : Json :=
 match nameFromJson j with
 | .ok n => nameJson (maps[n]?.getD n)
 | .error _ => match j with
  | .arr a => .arr (a.map (remapJson maps))
  | .obj kv => Json.mkObj (kv.toArray.toList.map fun (k,v) => (k,remapJson maps v))
  | _ => j

def main (args : List String) : IO Unit := do
 let some path := args.head? | throw <| IO.userError "pass compact fixture directory as argument"
 let base := System.FilePath.mk path
 initSearchPath (← findSysroot)
 let env ← importModules (loadExts := false) #[{module := `MainTheorems}] {} (trustLevel := 0)
 let replay ← readRows (base / "REPLAY_LITERAL_FIXTURES.jsonl")
 let mut ownerMaps : Std.HashMap String (Std.HashMap Name Name) := {}
 for group in replay do
  let owner ← IO.ofExcept <| group.getObjValAs? String "receiving_owner"
  let mut maps : Std.HashMap Name Name := {}
  for r in (← IO.ofExcept <| group.getObjValAs? (Array Json) "finite_name_map") do
   maps := maps.insert (← IO.ofExcept <| (r.getObjVal? "old").bind nameFromJson) (← IO.ofExcept <| (r.getObjVal? "new").bind nameFromJson)
  ownerMaps := ownerMaps.insert owner maps
 let choices ← IO.ofExcept <| (Json.parse (← IO.FS.readFile (base / "TWO_OWNER_CHOICES.json"))).bind Json.getArr?
 let choiceNames ← choices.mapM fun j => IO.ofExcept (nameFromJson j)
 let out ← IO.FS.Handle.mk (System.FilePath.mk "tools/verification-reports/ACTUAL_COMMON_KERNEL_RESULTS.jsonl") .write
 let mut total := 0
 for group in replay do
  for item in (← IO.ofExcept <| group.getObjValAs? (Array Json) "declarations") do
   let p ← IO.ofExcept <| item.getObjVal? "source_record"
   let n ← IO.ofExcept <| (p.getObjVal? "name").bind nameFromJson
   let some native := env.find? n | throw <| IO.userError s!"actual MainTheorems replay CI absent {n}"
   let ty ← IO.ofExcept <| (p.getObjVal? "type").bind exprFromJson
   let va ← IO.ofExcept <| (p.getObjVal? "value").bind exprFromJson
   let ls ← IO.ofExcept <| (p.getObjValAs? (Array Json) "levels").bind (fun a => a.toList.mapM nameFromJson)
   let alls ← IO.ofExcept <| (p.getObjValAs? (Array Json) "all").bind (fun a => a.toList.mapM nameFromJson)
   let kind ← IO.ofExcept <| p.getObjValAs? String "kind"
   let kindMeta ← match native with
    | .thmInfo d => pure (kind == "thm" && d.all == alls)
    | .defnInfo d => do
     let hints ← IO.ofExcept <| p.getObjValAs? (Array Json) "hints"
     let actual := match d.hints with | .opaque => #[toJson "opaque"] | .abbrev => #[toJson "abbrev"] | .regular n => #[toJson "regular",toJson n.toNat]
     pure (kind == "def" && d.all == alls && d.safety == .safe && hints == actual)
    | _ => pure false
   let bodyExact := (native.value? (allowOpaque := true)).any fun v => ExprStructEq.mk v == ExprStructEq.mk va
   let fs := [("role",toJson "replay"),("name",nameJson n),("kind_metadata_levels_exact",toJson (kindMeta && native.levelParams == ls)),("full_type_literal_identity",toJson (ExprStructEq.mk native.type == ExprStructEq.mk ty)),("body_literal_identity",toJson bodyExact),("approved_two_theorem_choice",toJson (choiceNames.contains n)),("old_body_at_full_type",← checkResult <| typedCheck env ty va),("actual_constant_at_full_type",← checkResult <| typedCheck env ty (mkConst n (ls.map Level.param)))]
   out.putStrLn <| Json.compress <| Json.mkObj fs
   total := total+1
 out.flush
 IO.println s!"REPLAY_DONE {total}"
 let mut partialNames : Std.HashSet Name := {}
 for filename in ["SAFE_LITERAL_FIXTURES.jsonl","FAMILY_PARTIAL_LITERAL_CIS.jsonl","CAPTURE_FROZEN_CIS.jsonl"] do
  let rows ← readRows (base / filename)
  for row in rows do
   let req ← IO.ofExcept <| row.getObjVal? "request"
   let role ← IO.ofExcept <| req.getObjValAs? String "role"
   let source ← IO.ofExcept <| req.getObjValAs? String "source"
   let n ← IO.ofExcept <| (row.getObjVal? "name").bind nameFromJson
   let ls ← IO.ofExcept <| (row.getObjValAs? (Array Json) "levels").bind (fun a => a.toList.mapM nameFromJson)
   let owner := (req.getObjValAs? String "owner").toOption.getD source
   let mut maps := ownerMaps[owner]?.getD {}
   if role == "capture" then
    for r in (← IO.ofExcept <| req.getObjValAs? (Array Json) "finite_literal_map") do
     maps := maps.insert (← IO.ofExcept <| (r.getObjVal? "old").bind nameFromJson) (← IO.ofExcept <| (r.getObjVal? "new").bind nameFromJson)
   let target := if role == "safe" then maps[n]?.getD n else if role == "family" then n.replacePrefix `EndpointPaidClassificationAux .anonymous else n
   let some native := env.find? target | throw <| IO.userError s!"actual common CI absent {target} {role}"
   let ty := remapFinite maps (← IO.ofExcept <| (row.getObjVal? "type").bind exprFromJson)
   let selected := mkConst target (ls.map Level.param)
   let mut fs := [("role",toJson role),("name",nameJson n),("actual_name",nameJson target),("source",toJson source),("levels_exact",toJson (ls == native.levelParams))]
   if role == "capture" then
    let value ← IO.ofExcept <| (row.getObjVal? "value").bind exprFromJson
    let body := remapFinite maps value
    fs := fs ++ [("capture_literal_full_type_exact",toJson (ExprStructEq.mk ty == ExprStructEq.mk native.type)),("capture_literal_body_exact",toJson ((native.value? (allowOpaque := true)).any fun v => ExprStructEq.mk v == ExprStructEq.mk body)),("capture_metadata_exact",toJson (remapJson maps (← IO.ofExcept <| row.getObjVal? "metadata") == metadata native))]
   if role == "partial" then
    partialNames := partialNames.insert target
    fs := fs ++ [("metadata_exact",toJson ((← IO.ofExcept <| row.getObjVal? "metadata") == metadata native)),("full_type_defeq",← defeqResult env ty native.type)]
   else fs := fs ++ [("actual_at_full_old_type",← checkResult <| typedCheck env ty selected)]
   if let some vj := (row.getObjVal? "value").toOption then
    let va := remapFinite maps (← IO.ofExcept <| exprFromJson vj)
    if role == "partial" then
     let some nv := native.value? (allowOpaque := true) | throw <| IO.userError "partial native body absent"
     fs := fs ++ [("full_body_defeq",← defeqResult env va nv),("body_defeq_constant",← defeqResult env va selected)]
    else
     fs := fs ++ [("old_body_typed",← checkResult <| typedCheck env ty va)]
     unless (← IO.ofExcept <| (row.getObjVal? "metadata").bind (fun m => m.getObjValAs? String "kind")) == "theorem" do
      fs := fs ++ [("operative_equality",← equalityResult env ty va selected)]
   if role == "family" then
    fs := fs ++ [("full_family_metadata_exact",toJson (remapJson maps (← IO.ofExcept <| row.getObjVal? "metadata") == metadata native))]
    if let some rj := (row.getObjValAs? (Array Json) "rules").toOption then
     let .recInfo rc := native | throw <| IO.userError "expected recursor"
     unless rj.size == rc.rules.length do throw <| IO.userError "recursor length drift"
     let mut results : Array Json := #[]
     for (old,new) in rj.toList.zip rc.rules do
      let rhs := remapFinite maps (← IO.ofExcept <| (old.getObjVal? "rhs").bind exprFromJson)
      let ctor := maps[(← IO.ofExcept <| (old.getObjVal? "ctor").bind nameFromJson)]?.getD (← IO.ofExcept <| (old.getObjVal? "ctor").bind nameFromJson)
      results := results.push <| Json.mkObj [("ctor_fields_exact",toJson (ctor == new.ctor && (← IO.ofExcept <| old.getObjValAs? Nat "nfields") == new.nfields)),("full_rule_rhs_defeq",← defeqResult env rhs new.rhs)]
     fs := fs ++ [("recursor_rules",toJson results)]
   out.putStrLn <| Json.compress <| Json.mkObj fs
   total := total+1
  out.flush
  IO.println s!"FIXTURE_DONE {filename} {rows.size}"
 for row in (← readRows (base / "GRAPH_LITERAL_FIXTURES.jsonl")) do
  let req ← IO.ofExcept <| row.getObjVal? "request"
  let ns ← IO.ofExcept <| req.getObjValAs? String "adapter_name"
  let n := ns.splitOn "." |>.foldl Name.str .anonymous
  let ty ← IO.ofExcept <| (row.getObjVal? "type").bind exprFromJson
  let ls ← IO.ofExcept <| (row.getObjValAs? (Array Json) "levels").bind (fun a => a.toList.mapM nameFromJson)
  out.putStrLn <| Json.compress <| Json.mkObj [("role",toJson "graph"),("name",nameJson n),("entire_old_type_kernel_check",← checkResult <| typedCheck env ty (mkConst n (ls.map Level.param)))]
  total := total+1
 out.flush
 let mut safeCount := 0
 let mut incoming : Array Json := #[]
 for (name,ci) in env.constants.toList do
  if ci.isUnsafe || ci.isPartial then continue
  safeCount := safeCount+1
  let mut hits := ci.type.foldConsts #[] fun n acc => if partialNames.contains n && !acc.contains n then acc.push n else acc
  if let some v := ci.value? (allowOpaque := true) then hits := v.foldConsts hits fun n acc => if partialNames.contains n && !acc.contains n then acc.push n else acc
  if let .recInfo r := ci then
   for rule in r.rules do hits := rule.rhs.foldConsts hits fun n acc => if partialNames.contains n && !acc.contains n then acc.push n else acc
  unless hits.isEmpty do incoming := incoming.push <| Json.mkObj [("safe_source",nameJson name),("partial_targets",toJson (hits.map nameJson))]
 IO.FS.writeFile (System.FilePath.mk "tools/verification-reports/ACTUAL_COMMON_SAFE_PARTIAL_BOUNDARY.json") (Json.pretty <| Json.mkObj [("safe_declarations_scanned",toJson safeCount),("partial_names",toJson (partialNames.toArray.map nameJson)),("incoming_safe_expression_references",toJson incoming),("scope",toJson "actual imported MainTheorems environment; types, bodies, full recursor rule RHS")])
 IO.println s!"COMPLETE actual MainTheorems {total} checks; safe boundary {safeCount} declarations, {incoming.size} incoming"
