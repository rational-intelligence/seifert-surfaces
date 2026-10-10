import Lean
import ExactPaidCodec
open Lean ExactPaidSource
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def toName (s : String) : Name := s.splitOn "." |>.foldl Name.str .anonymous
def sameExpr (a b : Expr) : Bool := Expr.equal a b && ExprStructEq.mk a == ExprStructEq.mk b
def typedCheck (env : Environment) (ty value : Expr) : Except Kernel.Exception Expr :=
 Kernel.check env {} (.letE `auditExactType ty value (.bvar 0) false)
def equalityCheck (env : Environment) (ty lhs rhs : Expr) : Except String Expr := do
 let st ← (Kernel.check env {} ty).mapError (fun _ => "type sort kernel check failed")
 let st ← (Kernel.whnf env {} st).mapError (fun _ => "type sort kernel WHNF failed")
 let .sort u := st | throw "expected sort"
 let target := mkApp3 (mkConst `Eq [u]) ty lhs rhs
 let refl := mkApp2 (mkConst `Eq.refl [u]) ty lhs
 (typedCheck env target refl).mapError (fun _ => "closed equality kernel check failed")
def resultJson (r : Except Kernel.Exception Expr) : IO Json := do
 match r with
 | .ok _ => return Json.mkObj [("status",toJson "PASS")]
 | .error e => return Json.mkObj [("status",toJson "FAIL"),("error",toJson (← (e.toMessageData {}).toString))]
def equalityJson (env : Environment) (ty lhs rhs : Expr) : IO Json := do
 match equalityCheck env ty lhs rhs with
 | .ok _ => return Json.mkObj [("status",toJson "PASS")]
 | .error msg =>
   let st := Kernel.check env {} ty
   let mut detail := msg
   if let .ok st := st then
    if let .ok (.sort u) := Kernel.whnf env {} st then
     let target := mkApp3 (mkConst `Eq [u]) ty lhs rhs
     let refl := mkApp2 (mkConst `Eq.refl [u]) ty lhs
     if let .error e := typedCheck env target refl then detail ← (e.toMessageData {}).toString
   return Json.mkObj [("status",toJson "FAIL"),("error",toJson detail)]
def hintsString : ReducibilityHints → String
 | .opaque => "opaque"
 | .abbrev => "abbrev"
 | .regular n => "regular " ++ toString n
private def metadata (ci : ConstantInfo) : Json :=
 let ns (xs : List Name) := toJson (xs.map nameJson)
 match ci with
 | .thmInfo v => Json.mkObj [("kind",toJson "theorem"),("all",ns v.all)]
 | .defnInfo v => Json.mkObj [("kind",toJson "definition"),("all",ns v.all),("hints",toJson (match v.hints with | .opaque => "opaque" | .abbrev => "abbrev" | .regular n => "regular " ++ toString n)),("safety",toJson (v.safety == .safe))]
 | .opaqueInfo v => Json.mkObj [("kind",toJson "opaque"),("all",ns v.all),("unsafe",toJson v.isUnsafe)]
 | .inductInfo v => Json.mkObj [("kind",toJson "inductive"),("all",ns v.all),("ctors",ns v.ctors),("numParams",toJson v.numParams),("numIndices",toJson v.numIndices),("numNested",toJson v.numNested),("isRec",toJson v.isRec),("unsafe",toJson v.isUnsafe),("isReflexive",toJson v.isReflexive)]
 | .ctorInfo v => Json.mkObj [("kind",toJson "constructor"),("induct",nameJson v.induct),("cidx",toJson v.cidx),("numParams",toJson v.numParams),("numFields",toJson v.numFields),("unsafe",toJson v.isUnsafe)]
 | .recInfo v => Json.mkObj [("kind",toJson "recursor"),("all",ns v.all),("numParams",toJson v.numParams),("numIndices",toJson v.numIndices),("numMotives",toJson v.numMotives),("numMinors",toJson v.numMinors),("k",toJson v.k),("unsafe",toJson v.isUnsafe)]
 | _ => Json.mkObj [("kind",toJson "FORBIDDEN")]
def main (args : List String) : IO Unit := do
 initSearchPath (← findSysroot)
 let base := System.FilePath.mk (args.head?.getD "tools/fixtures")
 let text ← IO.FS.readFile (base / "COMMON_UNION_APPROVED_LITERAL_GUARDS.jsonl")
 let env ← importModules (loadExts := false) #[{module := `MainTheorems}] {} (trustLevel := 0)
 let env := env.setExporting false
 let out ← IO.FS.Handle.mk (base / "COMMON_UNION_LITERAL_RECEIVING_KERNEL.jsonl") .write
 let mut failures := 0
 let mut total := 0
 let mut operative := 0
 let mut ruleCount := 0
 let mut absentCount := 0
 let inactive := toName "DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_mul_on_target"
 let exactFirst := "DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp"
 let exactSecond := "DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich.Compactness"
 let sourceText ← IO.FS.readFile (base / "ONE_ABSENT_UNUSED_BOUND_SOURCE_CIS.jsonl")
 let sources ← (sourceText.splitOn "\n" |>.filter (· != "")).toArray.mapM (fun l => IO.ofExcept (Json.parse l))
 unless sources.size == 2 do throw <| IO.userError "exact inactive two-provider source coverage drift"

 for line in text.splitOn "\n" do
  if line.isEmpty then continue
  let row ← IO.ofExcept <| Json.parse line
  let name ← IO.ofExcept <| row.getObjValAs? String "name"
  let n ← IO.ofExcept <| (row.getObjVal? "name_json").bind nameFromJson
  let lpJSON ← IO.ofExcept <| row.getObjValAs? (Array Json) "levels"
  let lp ← IO.ofExcept <| lpJSON.toList.mapM nameFromJson
  let oldTy ← IO.ofExcept <| (row.getObjVal? "old_type").bind exprFromJson
  let some chosen := env.find? n | do
   unless n == inactive && (← IO.ofExcept <| row.getObjValAs? String "first") == exactFirst && (← IO.ofExcept <| row.getObjValAs? String "second") == exactSecond && (← IO.ofExcept <| row.getObjValAs? Bool "is_theorem") do
    throw <| IO.userError s!"unapproved missing receiving declaration {name}"
   let mut oldBound := false
   let mut freshBound := false
   for source in sources do
    let module ← IO.ofExcept <| source.getObjValAs? String "module"
    let moduleName := toName module
    unless !env.header.moduleNames.contains moduleName do throw <| IO.userError "inactive source provider unexpectedly in Main"
    let sn ← IO.ofExcept <| (source.getObjVal? "name").bind nameFromJson
    let sl ← IO.ofExcept <| (source.getObjValAs? (Array Json) "levels").bind (fun a => a.toList.mapM nameFromJson)
    let st ← IO.ofExcept <| (source.getObjVal? "type").bind exprFromJson
    let sv ← IO.ofExcept <| (source.getObjVal? "value").bind exprFromJson
    let sm ← IO.ofExcept <| source.getObjVal? "metadata"
    let freshTy ← IO.ofExcept <| (row.getObjVal? "fresh_type").bind exprFromJson
    let expectedTy := if module == exactSecond then oldTy else freshTy
    let expectedMeta ← IO.ofExcept <| row.getObjVal? (if module == exactSecond then "old_metadata" else "fresh_metadata")
    unless sn == n && sl == lp && sameExpr st expectedTy && sm == expectedMeta && (← IO.ofExcept <| sm.getObjValAs? String "kind") == "theorem" do
     throw <| IO.userError "inactive exact complete CI binding mismatch"
    unless sameExpr sv (← IO.ofExcept <| exprFromJson (exprJson sv)) do throw <| IO.userError "inactive proof codec roundtrip drift"
    let pin ← IO.ofExcept <| source.getObjValAs? String "original_compiled_sha256"
    let srcPin ← IO.ofExcept <| source.getObjValAs? String "original_source_sha256"
    if module == exactFirst then
     unless pin == "0029120bf8a03957565b49321f200a75b2ddb0a6bd5243624211099d34c50f9e" && srcPin == "c94560cc7d7d03799a00f2f8039598730fd1f0e6c6052a6d821edc08dced203c" && !freshBound do throw <| IO.userError "inactive first source pin drift"
     freshBound := true
    else if module == exactSecond then
     unless pin == "1f306a959d70d23a5d6c7e38420570ca07932acb6e1cd353c8ccb5f444cb4fe7" && srcPin == "cf04052ebd4a6e50650eb8b1ef007fc65f6230c8c89a974eb320d0624ee0d3aa" && !oldBound do throw <| IO.userError "inactive second source pin drift"
     oldBound := true
    else throw <| IO.userError "inactive unexpected source provider"
   unless oldBound && freshBound do throw <| IO.userError "inactive source binding coverage incomplete"
   absentCount := absentCount+1
   total := total+1
   out.putStrLn <| Json.compress <| Json.mkObj [("name",toJson name),("coverage",toJson "ABSENT_UNUSED_AUXILIARY"),("exact_original_source_bindings",toJson true),("both_provider_modules_absent",toJson true),("old_type_actual_Main_PASS_claimed",toJson false),("raw_missing_retained",toJson true)]
   out.flush
   continue
  unless chosen.levelParams == lp do throw <| IO.userError s!"receiving levels drift {name}"
  let current := mkConst n (lp.map Level.param)
  let tyResult ← resultJson <| typedCheck env oldTy current
  let oldMeta ← IO.ofExcept <| row.getObjVal? "old_metadata"
  let newMeta := metadata chosen
  let mut metaSame := oldMeta == newMeta
  if name == "Schoenflies.IsChainFrom" || name == "Schoenflies.IsClosedChain" then
   let oldHints ← IO.ofExcept <| oldMeta.getObjValAs? String "hints"
   let newHints ← IO.ofExcept <| newMeta.getObjValAs? String "hints"
   unless oldHints == "regular 17" && newHints == "regular 20" do throw <| IO.userError "bounded reduction-height exception drift"
   let oldAll ← IO.ofExcept <| oldMeta.getObjVal? "all"
   let newAll ← IO.ofExcept <| newMeta.getObjVal? "all"
   let oldSafe ← IO.ofExcept <| oldMeta.getObjVal? "safety"
   let newSafe ← IO.ofExcept <| newMeta.getObjVal? "safety"
   metaSame := oldAll == newAll && oldSafe == newSafe
  let mut fields := [("name",toJson name),("old_type_selected_current",tyResult),("metadata_dimensions_pass",toJson metaSame),("old_metadata",oldMeta),("receiving_metadata",newMeta)]
  if let .ok valJson := row.getObjVal? "old_value" then
   operative := operative + 1
   let value ← IO.ofExcept <| exprFromJson valJson
   fields := fields ++ [("old_value_typing",← resultJson <| typedCheck env oldTy value),("old_value_current_closed_equality",← equalityJson env oldTy value current)]
  if let .ok rules := row.getObjValAs? (Array Json) "recursor_rules" then
   let .recInfo recursor := chosen | throw <| IO.userError s!"receiving recursor kind drift {name}"
   unless rules.size == recursor.rules.length do throw <| IO.userError s!"receiving recursor rule count drift {name}"
   ruleCount := ruleCount + rules.size
   let mut results : Array Json := #[]
   for (old,new) in rules.toList.zip recursor.rules do
    let ctor ← IO.ofExcept <| (old.getObjVal? "constructor").bind nameFromJson
    let nfields ← IO.ofExcept <| old.getObjValAs? Nat "nfields"
    unless ctor == new.ctor && nfields == new.nfields do throw <| IO.userError "receiving recursor rule shape drift"
    let rhs ← IO.ofExcept <| (old.getObjVal? "old_rhs").bind exprFromJson
    let rhsTy ← IO.ofExcept <| (Kernel.check env {} rhs).mapError (fun _ => "old recursor RHS type failure")
    results := results.push (← equalityJson env rhsTy rhs new.rhs)
   fields := fields ++ [("recursor_rhs_identities",toJson results)]
  let result := Json.mkObj fields
  let serialized := Json.compress result
  if !metaSame || (serialized.splitOn "\"FAIL\"").length > 1 then failures := failures + 1
  out.putStrLn serialized
  out.flush
  total := total + 1
 unless total == 929 && absentCount == 1 && operative == 396 && ruleCount == 39 && failures == 0 && !env.contains inactive do
  throw <| IO.userError s!"bounded coverage failure total={total} absent={absentCount} operative={operative} rules={ruleCount} failures={failures}"
 let mut scanned := 0
 let mut incoming : Array Json := #[]
 for (dn,ci) in env.constants.toList do
  scanned := scanned+1
  let typeHit := ci.type.foldConsts false fun n hit => hit || n == inactive
  let valueHit := (ci.value? (allowOpaque := true)).any fun v => v.foldConsts false fun n hit => hit || n == inactive
  let ruleHit := match ci with
   | .recInfo r => r.rules.any fun rule => rule.rhs.foldConsts false fun n hit => hit || n == inactive
   | _ => false
  if typeHit || valueHit || ruleHit then incoming := incoming.push <| Json.mkObj [("source",nameJson dn),("type",toJson typeHit),("value",toJson valueHit),("recursor_rule",toJson ruleHit)]
 IO.FS.writeFile (base / "COMMON_UNION_ONE_ABSENT_UNUSED_RECEIPT.json") (Json.pretty <| Json.mkObj [("total_records",toJson total),("present_full_type_PASS",toJson (total-absentCount)),("absent_unused_original_auxiliary",toJson absentCount),("operative_closed_equality_PASS",toJson operative),("complete_recursor_RHS_PASS",toJson ruleCount),("raw_missing_retained",toJson true),("environment_declarations_scanned",toJson scanned),("incoming_type_value_recursor_references",toJson incoming),("inactive_name",nameJson inactive),("scope",toJson "actual MainTheorems:928present full types plus1explicit absent unused old auxiliary; no929raw-typePASS claim")])
 unless scanned > 0 && incoming.isEmpty do throw <| IO.userError "inactive original auxiliary has incoming operative references"
 IO.println s!"RECEIVING_LITERAL_KERNEL total={total} present=928 absent_unused=1 operative={operative} recursor_rhs={ruleCount} failures=0 scanned={scanned} incoming=0"
