import project.OriginalSection62
import GeometrySupportV510
import EndpointSupportV510


section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Lean Elab Command
run_cmd do
  let owned := System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/target/Original62WholeProofData"
  let paidObjects := System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/target/Original62WholeProofData/objects"
  let moduleName := (← getEnv).header.mainModule
  let native := (← getEnv).setExporting false
  let savedPath ← liftIO searchPathRef.get
  liftIO <| searchPathRef.set (paidObjects :: savedPath)
  let paid ← liftIO <| importModules (loadExts := false)
    #[{module := `ActualOriginalSection62CompletionV940}] {} (trustLevel := 0)
  liftIO <| searchPathRef.set savedPath
  let paid := paid.setExporting false
  let roots := #[`CompressionActualWholeMatchedNativePrerequisitesV933.given_original_disk_whole_matched_native_realization,
    `CompressionActualOriginalFullMatchedSurfaceProductV935.given_original_full_matched_surface_product,
    `CompressionActualOriginalNativeRealizationV939.given_original_annulus_native_realization,
    `CompressionActualOriginalSection62CompletionV940.original_6_2_with_actual_original_annulus_realization]
  let mut names := roots
  let mut pending : Array ConstantInfo := #[]
  let mut seen : Std.HashSet Name := {}
  let mut inherited : Array String := #[]
  while !names.isEmpty do
    let name := names.back!
    names := names.pop
    if seen.contains name then continue
    seen := seen.insert name
    if name == `sorryAx then throwError "Unpaid geometry dependency {name}"
    let some ci := paid.find? name | throwError "Paid geometry dependency missing {name}"
    if let some actual := native.constants.find? name then
      let sameType := actual.levelParams == ci.levelParams && Expr.equal actual.type ci.type &&
        ExprStructEq.mk actual.type == ExprStructEq.mk ci.type
      let sameBody := match ci with
        | .defnInfo d => match actual with
          | .defnInfo a => Expr.equal a.value d.value && ExprStructEq.mk a.value == ExprStructEq.mk d.value
          | _ => false
        | .opaqueInfo d => match actual with
          | .opaqueInfo a => Expr.equal a.value d.value && ExprStructEq.mk a.value == ExprStructEq.mk d.value
          | _ => false
        | _ => true
      unless sameType && sameBody do
        throwError "Existing exact receiver dependency differs {name}; type={sameType}; body={sameBody}"
      inherited := inherited.push name.toString
      continue
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial geometry dependency {name}"
    match ci with
    | .inductInfo d =>
      pending := pending.push ci
      names := names ++ d.all.toArray ++ d.ctors.toArray ++ ci.type.getUsedConstantsAsSet.toArray
    | .ctorInfo d => names := names.push d.induct ++ ci.type.getUsedConstantsAsSet.toArray
    | .recInfo d => names := names ++ d.all.toArray ++ ci.type.getUsedConstantsAsSet.toArray
    | .defnInfo d =>
      pending := pending.push ci
      names := names ++ (ci.type.getUsedConstantsAsSet.merge d.value.getUsedConstantsAsSet).toArray
    | .thmInfo d =>
      pending := pending.push ci
      names := names ++ (ci.type.getUsedConstantsAsSet.merge d.value.getUsedConstantsAsSet).toArray
    | .opaqueInfo d =>
      pending := pending.push ci
      names := names ++ (ci.type.getUsedConstantsAsSet.merge d.value.getUsedConstantsAsSet).toArray
    | _ => throwError "Unpaid geometry primitive {name}"
  let mut jobs : Array (Name × Declaration × Array Name) := #[]
  for ci in pending do
    let mut deps := ci.type.getUsedConstantsAsSet
    let declaration ← match ci with
      | .defnInfo d =>
        deps := deps.merge d.value.getUsedConstantsAsSet
        pure (.defnDecl d)
      | .thmInfo d =>
        deps := deps.merge d.value.getUsedConstantsAsSet
        pure (.thmDecl d)
      | .opaqueInfo d =>
        deps := deps.merge d.value.getUsedConstantsAsSet
        pure (.opaqueDecl d)
      | .inductInfo d => do
        let mut types : List InductiveType := []
        for owner in d.all do
          let some (.inductInfo i) := paid.find? owner | throwError "Paid inductive owner missing {owner}"
          deps := deps.merge i.type.getUsedConstantsAsSet
          let mut ctors : List Constructor := []
          for ctor in i.ctors do
            let some c := paid.find? ctor | throwError "Paid constructor missing {ctor}"
            deps := deps.merge c.type.getUsedConstantsAsSet
            ctors := ctors ++ [{name := ctor, type := c.type}]
          types := types ++ [{name := owner, type := i.type, ctors := ctors}]
        for owner in d.all do deps := deps.erase owner
        pure (.inductDecl d.levelParams d.numParams types d.isUnsafe)
      | _ => throwError "Unexpected paid geometry dependency kind {ci.name}"
    jobs := jobs.push (ci.name, declaration, deps.toArray)
  let mut round := 0
  while !jobs.isEmpty do
    round := round + 1
    let mut next := #[]
    let mut progress := false
    for (name, declaration, deps) in jobs do
      let current := (← getEnv).setExporting false
      if (current.constants.find? name).isSome then progress := true
      else if deps.any (fun n => (current.constants.find? n).isNone) then
        next := next.push (name, declaration, deps)
      else
        liftCoreM <| addDecl declaration
        progress := true
    liftIO <| IO.FS.writeFile (owned / s!"logs/{moduleName}.Original62WholeV508.progress.txt")
      s!"Round {round}; remaining {next.size}; paid {jobs.size-next.size}\n"
    unless progress do
      let current := (← getEnv).setExporting false
      let missing := next.map (fun (n,_,ds) => (n.toString,ds.filter (fun d => (current.find? d).isNone) |>.map Name.toString))
      liftIO <| IO.FS.writeFile (owned / s!"logs/{moduleName}.UnresolvedDependencies.json") ((toJson missing).pretty ++ "\n")
      throwError "Unresolved exact kernel dependencies; see owned logs/UnresolvedDependencies.json"
    jobs := next
  let mut restored : Array String := #[]
  for name in seen.toArray do
    if let some (.defnInfo _) := paid.find? name then
      let status := getReducibilityStatusCore paid name
      let currentStatus := getReducibilityStatusCore (← getEnv) name
      if status != currentStatus then
        liftCoreM <| setReducibilityStatus name status
        restored := restored.push name.toString
  liftIO <| IO.FS.writeFile (owned / s!"logs/{moduleName}.Original62WholeV508.restored-reducibility.json")
    ((toJson restored).pretty ++ "\n")
  let current := (← getEnv).setExporting false
  for ci in pending do
    let some actual := current.constants.find? ci.name | throwError "Replayed geometry declaration absent {ci.name}"
    unless actual.levelParams == ci.levelParams && Expr.equal actual.type ci.type &&
      ExprStructEq.mk actual.type == ExprStructEq.mk ci.type do
      throwError "Literal replayed geometry type changed {ci.name}"
    if let some value := ci.value? (allowOpaque := true) then
      let some actualValue := actual.value? (allowOpaque := true) | throwError "Replayed body absent {ci.name}"
      unless Expr.equal actualValue value && ExprStructEq.mk actualValue == ExprStructEq.mk value do
        throwError "Literal replayed geometry proof/body changed {ci.name}"

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
      ("replayed_count",toJson pending.size),("inherited_count",toJson inherited.size),
      ("providers",toJson providers)]).pretty ++ "\n")
  logInfo m!"PASS exact receiver: {pending.size} literal paid kernel declarations; {inherited.size} native providers preserved"
end

