import Original62CompletionV510
import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command
run_cmd do
  let owned := System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/target/Original62WholeProofData"
  let paidObjects := System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/target/Original62WholeProofData/objects"
  let moduleName := (← getEnv).header.mainModule
  let savedPath ← liftIO searchPathRef.get
  liftIO <| searchPathRef.set (paidObjects :: savedPath)
  let paid ← liftIO <| importModules (loadExts := false) #[{module := `ActualOriginalSection62CompletionV940}] {} (trustLevel := 0)
  liftIO <| searchPathRef.set savedPath
  let paid := paid.setExporting false
  let current := (← getEnv).setExporting false
  let records ← liftIO <| IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/target/Original62WholeProofData/evidence/FULL_RAW_OPERATIVE_PROVIDER_EQUALITY.json"
  let json ← ofExcept <| Json.parse records
  let rows ← ofExcept <| json.getObjValAs? (Array Json) "providers"
  let mut seen : Std.HashSet Name := {}
  let mut inherited : Array String := #[]
  let mut replayedCount : Nat := 0
  let mut inheritedCount : Nat := 0
  for row in rows do
    let nameString ← ofExcept <| row.getObjValAs? String "name"
    let name := nameString.toName
    seen := seen.insert name
    let wasInherited ← ofExcept <| row.getObjValAs? Bool "inherited"
    if wasInherited then
      inherited := inherited.push nameString
      inheritedCount := inheritedCount + 1
    else
      replayedCount := replayedCount + 1
    let some p := paid.find? name | throwError "Paid declaration missing {name}"
    let some c := current.find? name | throwError "Reimported declaration missing {name}"
    if !wasInherited then
      if let some pv := p.value? (allowOpaque := true) then
        let some cv := c.value? (allowOpaque := true) | throwError "Reimported proof/body missing {name}"
        unless Expr.equal pv cv && ExprStructEq.mk pv == ExprStructEq.mk cv do
          throwError "Reimported proof/body changed {name}"
  let mut providers : Array Json := #[]
  for name in seen.toArray do
    let some original := paid.find? name | throwError "Missing paid declaration {name}"
    let some actual := current.constants.find? name | throwError "Missing receiver declaration {name}"
    unless actual.levelParams == original.levelParams &&
      Expr.equal actual.type original.type && ExprStructEq.mk actual.type == ExprStructEq.mk original.type do
      throwError "Full raw closure type differs {name}"
    let operative := match original with
      | .defnInfo _ => true
      | .opaqueInfo _ => true
      | _ => false
    if operative then
      let some v := original.value? (allowOpaque := true) | throwError "Missing operative value {name}"
      let some a := actual.value? (allowOpaque := true) | throwError "Missing receiver value {name}"
      unless Expr.equal a v && ExprStructEq.mk a == ExprStructEq.mk v do
        throwError "Full raw closure operative value differs {name}"
    let oldOwner : String := match paid.getModuleIdxFor? name with
      | some i => paid.header.moduleNames[i.toNat]!.toString
      | none => "LOCAL"
    let newOwner : String := match current.getModuleIdxFor? name with
      | some i => current.header.moduleNames[i.toNat]!.toString
      | none => moduleName.toString
    if inherited.contains name.toString && oldOwner != newOwner &&
        !(#["project.OriginalSection62", "GeometrySupportV510", "EndpointSupportV510"].contains newOwner) then
      throwError "Inherited native provider changed {name}: {oldOwner} -> {newOwner}"
    providers := providers.push <| Json.mkObj [
      ("name",toJson name.toString),("type_literal",toJson true),
      ("operative",toJson operative),("operative_value_literal",toJson true),
      ("paid_provider",toJson oldOwner),("receiver_provider",toJson newOwner),
      ("inherited",toJson (inherited.contains name.toString))]
  let (approved,_region) ← liftIO <| readModuleData (paidObjects / "OriginalSection62.olean")
  let mut originalCount : Nat := 0
  for ci in approved.constants do
    if ci.name == `SeifertSurfaces.OriginalEndpoints.original_6_2 then continue
    let some a := current.constants.find? ci.name | throwError "Original operative declaration missing {ci.name}"
    unless a.levelParams == ci.levelParams && Expr.equal a.type ci.type &&
      ExprStructEq.mk a.type == ExprStructEq.mk ci.type do
      throwError "Original entire raw declaration type changed {ci.name}"
    let operative := match ci with
      | .defnInfo _ => true
      | .opaqueInfo _ => true
      | _ => false
    if operative then
      if let some v := ci.value? (allowOpaque := true) then
        let some av := a.value? (allowOpaque := true) | throwError "Original operative body missing {ci.name}"
        unless Expr.equal av v && ExprStructEq.mk av == ExprStructEq.mk v do
          throwError "Original operative body changed {ci.name}"
    originalCount := originalCount + 1
  logInfo m!"PASS entire original receiver declarations: {originalCount} literal raw types and operative values"
  liftIO <| IO.FS.writeFile (owned / s!"logs/{moduleName}.raw.json")
    ((Json.mkObj [("status",toJson "PASS"),("closure_count",toJson seen.size),
      ("replayed_count",toJson replayedCount),("inherited_count",toJson inheritedCount),
      ("providers",toJson providers)]).pretty ++ "\n")
  logInfo m!"PASS exact receiver: {replayedCount} literal paid kernel declarations; {inheritedCount} inherited declarations compared"
  let n := `SeifertSurfaces.OriginalEndpoints.original_6_2
  let some original := approved.constants.find? (fun c => c.name == n) | throwError "Original root absent"
  let some actual := current.find? n | throwError "Completed root absent"
  unless actual.levelParams == original.levelParams && Expr.equal actual.type original.type && ExprStructEq.mk actual.type == ExprStructEq.mk original.type do
    throwError "Reimported full original root raw type changed"
  logInfo "PASS reimported full original root raw type literal"
#print axioms SeifertSurfaces.OriginalEndpoints.original_6_2
#print axioms CompressionActualWholeMatchedNativePrerequisitesV933.given_original_disk_whole_matched_native_realization
#print axioms CompressionActualOriginalFullMatchedSurfaceProductV935.given_original_full_matched_surface_product
#print axioms CompressionActualOriginalNativeRealizationV939.given_original_annulus_native_realization
#print axioms CompressionActualOriginalSection62CompletionV940.original_6_2_with_actual_original_annulus_realization
