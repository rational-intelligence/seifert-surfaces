import MainTheorems
import ExactPaidCodec
import Lean
open Lean Elab Command Meta ExactPaidSource
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
run_cmd do
 let text ← liftIO <| IO.FS.readFile "tools/fixtures/A5_COMMON_PROVIDER_FINITE53_MAP.json"
 let input ← Lean.ofExcept <| Json.parse text
 let rows ← Lean.ofExcept <| input.getObjValAs? (α := Array Json) "rows"
 let mut mapping : NameMap Name := {}
 for inputRow in rows do
  let original ← Lean.ofExcept <| inputRow.getObjVal? "old_record"
  let old ← Lean.ofExcept <| nameFromJson (← Lean.ofExcept <| original.getObjVal? "name")
  let curr ← Lean.ofExcept <| nameFromJson (← Lean.ofExcept <| inputRow.getObjVal? "proposed_current_name_json")
  mapping := mapping.insert old curr
 let mapExpr (e : Expr) : Expr := e.replace fun node =>
  match node with
  | .const n ls => (mapping.find? n).map fun curr => .const curr ls
  | _ => none
 let mut exported : Array Json := #[]
 let mut failed : Nat := 0
 for inputRow in rows do
  let row ← Lean.ofExcept <| inputRow.getObjVal? "old_record"
  let currentN ← Lean.ofExcept <| nameFromJson (← Lean.ofExcept <| inputRow.getObjVal? "proposed_current_name_json")  let n ← Lean.ofExcept <| nameFromJson (← Lean.ofExcept <| row.getObjVal? "name")
  let rawOldTy ← Lean.ofExcept <| exprFromJson (← Lean.ofExcept <| row.getObjVal? "type")
  let oldTy := mapExpr rawOldTy
  let lpj ← Lean.ofExcept <| row.getObjValAs? (α := Array Json) "levels"
  let lp ← Lean.ofExcept <| lpj.toList.mapM nameFromJson
  let some ci := ((← getEnv).setExporting false).find? currentN | do
   exported := exported.push <| Json.mkObj [("print_name",toJson n.toString),("current_name",toJson currentN.toString),("status",toJson "COUNTERPART_ABSENT_NO_IDENTITY_CLAIM")]
   logInfo m!"ABSENT explicit candidate {n} -> {currentN}"
   continue
  let newTy := ci.type.instantiateLevelParams ci.levelParams (lp.map Level.param)
  let mut fields := [("name",nameJson n),("print_name",toJson n.toString),("raw_expected_type",exprJson rawOldTy),("expected_type",exprJson oldTy),("current_name",toJson currentN.toString),("actual_type",exprJson newTy),("old_levels",toJson (lp.map Name.toString)),("current_levels",toJson (ci.levelParams.map Name.toString))]
  try
   let data ← liftTermElabM do
    let ty ← mkEq oldTy newTy
    let pr ← mkEqRefl oldTy
    return (ty,pr)
   let nm := Name.mkSimple ("A5FiniteCommonTypeIdentity_" ++ n.toString.replace "." "_")
   liftCoreM <| addDecl <| .thmDecl {name := nm,levelParams := lp,type := data.1,value := data.2}
   let axs ← collectAxioms nm
   unless axs.all (fun a => #[`propext,`Classical.choice,`Quot.sound].contains a) do throwError "Unexpected axioms {axs}"
   fields := fields ++ [("type_kernel_identity",toJson "PASS"),("type_axioms",toJson (axs.map Name.toString))]
   logInfo m!"PASS closed kernel type identity {n}"
  catch err =>
   failed := failed + 1
   let msg ← err.toMessageData.toString
   fields := fields ++ [("type_kernel_identity",toJson "FAIL"),("type_error",toJson msg)]
   logInfo m!"FAIL closed kernel type identity {n}: {msg}"
  if let .ok oldVJ := row.getObjVal? "value" then
   let rawOldV ← Lean.ofExcept <| exprFromJson oldVJ
   let oldV := mapExpr rawOldV
   let some v := ci.value? (allowOpaque := true) | throwError "Missing operative value {n}"
   let newV := v.instantiateLevelParams ci.levelParams (lp.map Level.param)
   fields := fields ++ [("raw_expected_value",exprJson rawOldV),("expected_value",exprJson oldV),("actual_value",exprJson newV)]
   try
    let data ← liftTermElabM do
     let ty ← mkEq oldV newV
     let pr ← mkEqRefl oldV
     return (ty,pr)
    let nm := Name.mkSimple ("A5FiniteCommonValueIdentity_" ++ n.toString.replace "." "_")
    liftCoreM <| addDecl <| .thmDecl {name := nm,levelParams := lp,type := data.1,value := data.2}
    let axs ← collectAxioms nm
    unless axs.all (fun a => #[`propext,`Classical.choice,`Quot.sound].contains a) do throwError "Unexpected axioms {axs}"
    fields := fields ++ [("value_kernel_identity",toJson "PASS"),("value_axioms",toJson (axs.map Name.toString))]
    logInfo m!"PASS closed kernel operative identity {n}"
   catch err =>
    failed := failed + 1
    let msg ← err.toMessageData.toString
    fields := fields ++ [("value_kernel_identity",toJson "FAIL"),("value_error",toJson msg)]
    logInfo m!"FAIL closed kernel operative identity {n}: {msg}"
  exported := exported.push <| Json.mkObj fields
 liftIO <| IO.FS.writeFile "tools/verification-reports/COMMON53_KERNEL_RESULTS.json" (Json.compress (toJson exported))
 if failed > 0 then logError m!"Finite identity audit has {failed} failures; no blanket acceptance"
