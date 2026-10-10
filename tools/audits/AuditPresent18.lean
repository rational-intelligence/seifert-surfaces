import MainTheorems
import ExactPaidCodec
import Lean
open Lean Elab Command Meta ExactPaidSource
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
private def mapWeakProofSlots (e : Expr) : Expr := e.replace fun node =>
 match node with
 | .const n ls =>
  if n == `SeifertSurfaces.WeakSchauder.H01Space._proof_4 then some (.const `SeifertSurfaces.WeakSchauder.H01Space._proof_5 ls)
  else if n == `SeifertSurfaces.WeakSchauder.H01Space._proof_5 then some (.const `SeifertSurfaces.WeakSchauder.H01Space._proof_6 ls)
  else if n == `SeifertSurfaces.WeakSchauder.H01Space._proof_6 then some (.const `SeifertSurfaces.WeakSchauder.H01Space._proof_7 ls)
  else if n == `SeifertSurfaces.WeakSchauder.H01Space._proof_7 then some (.const `SeifertSurfaces.WeakSchauder.H01Space._proof_8 ls)
  else none
 | _ => none
run_cmd do
 let text ← liftIO <| IO.FS.readFile "tools/fixtures/EXPECTED_PRESENT18.json"
 let rows ← Lean.ofExcept <| (← Lean.ofExcept <| Json.parse text).getArr?
 let mut exported : Array Json := #[]
 let mut failed : Nat := 0
 for row in rows do
  let n ← Lean.ofExcept <| nameFromJson (← Lean.ofExcept <| row.getObjVal? "name")
  let rawOldTy ← Lean.ofExcept <| exprFromJson (← Lean.ofExcept <| row.getObjVal? "type")
  let isWeakRow := (#["SeifertSurfaces.WeakSchauder.H01Space._proof_6","SeifertSurfaces.WeakSchauder.H01Space._proof_5","SeifertSurfaces.WeakSchauder.H01Space._proof_4","SeifertSurfaces.WeakSchauder.H01Space","SeifertSurfaces.WeakSchauder.H01Space._proof_7","SeifertSurfaces.WeakSchauder.frozenForm","SeifertSurfaces.WeakSchauder.H01Space_eq_closure_smoothPairs","SeifertSurfaces.WeakSchauder.smoothPairSubmodule","SeifertSurfaces.WeakSchauder.witnessPair_smul","SeifertSurfaces.WeakSchauder.smoothPairSubmodule._proof_4","SeifertSurfaces.WeakSchauder.H01Space.eq_1","SeifertSurfaces.WeakSchauder.frozenLoad","SeifertSurfaces.WeakSchauder.H01Space_complete"]).contains n.toString
  let oldTy := if isWeakRow then mapWeakProofSlots rawOldTy else rawOldTy
  let currentN := if isWeakRow then (mapWeakProofSlots (.const n [])).constName! else n
  let lpj ← Lean.ofExcept <| row.getObjValAs? (α := Array Json) "levels"
  let lp ← Lean.ofExcept <| lpj.toList.mapM nameFromJson
  let some ci := ((← getEnv).setExporting false).find? currentN | throwError "Missing present record {n}"
  let newTy := ci.type.instantiateLevelParams ci.levelParams (lp.map Level.param)
  let mut fields := [("name",nameJson n),("print_name",toJson n.toString),("raw_expected_type",exprJson rawOldTy),("expected_type",exprJson oldTy),("current_corresponding_name",toJson currentN.toString),("actual_type",exprJson newTy),("old_levels",toJson (lp.map Name.toString)),("current_levels",toJson (ci.levelParams.map Name.toString))]
  try
   let data ← liftTermElabM do
    let ty ← mkEq oldTy newTy
    let pr ← mkEqRefl oldTy
    return (ty,pr)
   let nm := Name.mkSimple ("A5BoundedTypeIdentity_" ++ n.toString.replace "." "_")
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
   let oldV := if isWeakRow then mapWeakProofSlots rawOldV else rawOldV
   let some v := ci.value? (allowOpaque := true) | throwError "Missing operative value {n}"
   let newV := v.instantiateLevelParams ci.levelParams (lp.map Level.param)
   fields := fields ++ [("raw_expected_value",exprJson rawOldV),("expected_value",exprJson oldV),("actual_value",exprJson newV)]
   try
    let data ← liftTermElabM do
     let ty ← mkEq oldV newV
     let pr ← mkEqRefl oldV
     return (ty,pr)
    let nm := Name.mkSimple ("A5BoundedValueIdentity_" ++ n.toString.replace "." "_")
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
 liftIO <| IO.FS.writeFile "tools/verification-reports/PRESENT18_KERNEL_RESULTS.json" (Json.compress (toJson exported))
 if failed > 0 then logError m!"Finite identity audit has {failed} failures; no blanket acceptance"

run_cmd do
 for n in #[`SeifertSurfaces.WeakSchauder.H01Space._proof_5, `SeifertSurfaces.WeakSchauder.H01Space._proof_6, `SeifertSurfaces.WeakSchauder.H01Space._proof_7, `SeifertSurfaces.WeakSchauder.H01Space._proof_8] do
  let some ci := ((← getEnv).setExporting false).find? n | throwError "Missing explicitly mapped proof slot {n}"
  let isTheorem := match ci with | .thmInfo _ => true | _ => false
  unless isTheorem do throwError "Explicit slot is not a theorem: {n}"
  logInfo m!"EXPLICIT ACTUAL CI {n}: {ci.type}"
