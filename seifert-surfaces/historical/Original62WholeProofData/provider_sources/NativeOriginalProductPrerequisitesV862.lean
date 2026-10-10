import NativeGeometryReplayV763
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Lean Elab Command

/- Kernel replay of existing paid geometry in the canonical native environment.
   No old declaration is rewritten or normalized. Canonical data declarations
   are retained with their exact original types and operative values; mismatches
   with the old environment are recorded rather than treated as identity. Every
   missing proof/definition is rechecked with its literal captured term. -/
run_cmd do
  let owned := System.FilePath.mk
    "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_compression_smoothing_and_topology_large/continuation_v436"
  let native := (← getEnv).setExporting false
  let mut nativePins : Std.HashMap Name ConstantInfo := {}
  let nativeLibrary := System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/target/.lake/build/lib/lean"
  for modName in #["Foundations", "LinkExterior", "CompressionContracts"] do
    let (data, _region) ← liftIO <| readModuleData (nativeLibrary / (modName ++ ".olean"))
    for ci in data.constants do nativePins := nativePins.insert ci.name ci
  let (record, _region) ← liftIO <| readModuleData
    "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/original62_proof_v477/native_objects/OriginalSection62.olean"
  for ci in record.constants do nativePins := nativePins.insert ci.name ci
  for (name, pin) in nativePins.toList do
    let some actual := native.find? name | throwError "Native original pin missing {name}"
    unless actual.levelParams == pin.levelParams && Expr.equal actual.type pin.type &&
      ExprStructEq.mk actual.type == ExprStructEq.mk pin.type do
      throwError "Native original pin type differs {name}"
    if let some value := pin.value? (allowOpaque := true) then
      let some actualValue := actual.value? (allowOpaque := true) |
        throwError "Native original pin body missing {name}"
      unless Expr.equal actualValue value && ExprStructEq.mk actualValue == ExprStructEq.mk value do
        throwError "Native original pin body differs {name}"
  let savedPath ← liftIO searchPathRef.get
  liftIO <| searchPathRef.set
    ((owned / "native_contract_v728") :: (owned / "project/.lake/build/lib/lean") :: savedPath)
  let paid ← liftIO <| importModules (loadExts := false) #[
    {module := `ActualWholeRoundedProductQuotientV654}] {} (trustLevel := 0)
  liftIO <| searchPathRef.set savedPath
  let paid := paid.setExporting false
  let roots := #[
    `CompressionActualWholeRoundedProductQuotient.given_original_disk_whole_rounded_product_quotient]
  let mut names := roots
  let mut pending : Array ConstantInfo := #[]
  let mut seen : Std.HashSet Name := {}
  let mut mismatches : Array String := #[]
  while !names.isEmpty do
    let name := names.back!
    names := names.pop
    if seen.contains name then continue
    seen := seen.insert name
    if name == `sorryAx then throwError "Unpaid geometry dependency {name}"
    let some ci := paid.find? name | throwError "Paid geometry dependency missing {name}"
    if let some actual := native.find? name then
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
        unless nativePins.contains name do
          throwError "Unpinned existing native dependency differs {name}"
        mismatches := mismatches.push s!"{name}: old type identical={sameType}; old body identical={sameBody}; retained exact canonical native pin"
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
  liftIO <| IO.FS.writeFile (owned / "logs/NativeOriginalProductPrerequisitesV862.old-native-mismatches.txt")
    (String.intercalate "\n" mismatches.toList ++ "\n")
  liftIO <| IO.FS.writeFile (owned / "logs/NativeOriginalProductPrerequisitesV862.used-constants.json")
    ((toJson (seen.toArray.map Name.toString)).pretty ++ "\n")
  liftIO <| IO.FS.writeFile (owned / "logs/NativeOriginalProductPrerequisitesV862.progress.txt")
    s!"Closure collected: {pending.size} missing declarations; {mismatches.size} retained canonical pin mismatches\n"
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
      if (current.find? name).isSome then progress := true
      else if deps.any (fun n => (current.find? n).isNone) then
        next := next.push (name, declaration, deps)
      else
        liftCoreM <| addDecl declaration
        progress := true
    liftIO <| IO.FS.writeFile (owned / "logs/NativeOriginalProductPrerequisitesV862.progress.txt")
      s!"Round {round}; remaining {next.size}; paid {jobs.size-next.size}\n"
    unless progress do throwError "Unresolved paid geometry closure {next.map (·.1)}"
    jobs := next
  let mut restored : Array String := #[]
  for name in seen.toArray do
    if nativePins.contains name then continue
    if let some (.defnInfo _) := paid.find? name then
      let status := getReducibilityStatusCore paid name
      let currentStatus := getReducibilityStatusCore (← getEnv) name
      if status != currentStatus then
        liftCoreM <| setReducibilityStatus name status
        restored := restored.push name.toString
  liftIO <| IO.FS.writeFile (owned / "logs/NativeOriginalProductPrerequisitesV862.restored-reducibility.json")
    ((toJson restored).pretty ++ "\n")
  let current := (← getEnv).setExporting false
  for ci in pending do
    let some actual := current.find? ci.name | throwError "Replayed geometry declaration absent {ci.name}"
    unless actual.levelParams == ci.levelParams && Expr.equal actual.type ci.type &&
      ExprStructEq.mk actual.type == ExprStructEq.mk ci.type do
      throwError "Literal replayed geometry type changed {ci.name}"
    if let some value := ci.value? (allowOpaque := true) then
      let some actualValue := actual.value? (allowOpaque := true) | throwError "Replayed body absent {ci.name}"
      unless Expr.equal actualValue value && ExprStructEq.mk actualValue == ExprStructEq.mk value do
        throwError "Literal replayed geometry proof/body changed {ci.name}"
  for modName in current.header.moduleNames do
    if modName == `CompressionComponentRelease then
      throwError "Old contract defining module entered actual native environment"
  logInfo m!"PASS: {pending.size} exact paid geometry declarations rechecked by kernel; {nativePins.size} exact canonical pins retained; old defining module absent"

#print axioms CompressionActualWholeRoundedProductQuotient.given_original_disk_whole_rounded_product_quotient
