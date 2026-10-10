import OriginalA5ScaffoldV464
import Lean
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array Name := #[`SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A5_original]
  for root in roots do
    let some ci := env.find? root | throwError "missing original target {root}"
    let some proof := ci.value? (allowOpaque := true) | throwError "missing original proof {root}"
    if proof.hasFVar || proof.hasMVar then throwError "unclosed original proof {root}"
    liftTermElabM do Lean.Meta.checkWithKernel proof
    let axes ← liftCoreM <| collectAxioms root
    for ax in axes do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "unexpected original axiom {root}: {ax}"
  let mut recursorsByInductive : Std.HashMap Name (Array Name) := {}
  for data in env.header.moduleData do
    for name in data.constNames do
      if let some (.recInfo r) := env.find? name then
        for ind in r.all do
          recursorsByInductive := recursorsByInductive.insert ind
            ((recursorsByInductive[ind]?.getD #[]).push name)
  let mut rows : Array Json := #[]
  let mut actualAxioms : Array String := #[]
  let mut pending : Array Name := roots
  let mut seen : NameSet := {}
  let mut index : Nat := 0
  while index < pending.size do
    let n := pending[index]!
    index := index + 1
    if seen.contains n then continue
    seen := seen.insert n
    let some dep := env.find? n | throwError "missing actual closure constant {n}"
    if let .axiomInfo _ := dep then actualAxioms := actualAxioms.push n.toString
    let owner := ((env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i]!.toString).getD "<current>"
    rows := rows.push (Json.mkObj [("name",toJson n.toString),("module",toJson owner),
      ("ordered_universes",toJson (dep.levelParams.map Name.toString))])
    let mut deps := dep.type.getUsedConstantsAsSet.merge
      ((dep.value? (allowOpaque := true)).map Expr.getUsedConstantsAsSet |>.getD {})
    match dep with
    | .inductInfo d =>
      deps := d.ctors.foldl (fun acc c => acc.insert c) deps
      deps := d.all.foldl (fun acc c => acc.insert c) deps
      deps := (recursorsByInductive[n]?.getD #[]).foldl (fun acc c => acc.insert c) deps
      if let some st := getStructureInfo? env n then
        for f in st.fieldInfo do
          deps := deps.insert f.projFn
          if let some parent := f.subobject? then deps := deps.insert parent
        for p in st.parentInfo do deps := (deps.insert p.structName).insert p.projFn
    | .recInfo d =>
      deps := d.all.foldl (fun acc c => acc.insert c) deps
      for rule in d.rules do
        deps := deps.insert rule.ctor
        deps := deps.merge rule.rhs.getUsedConstantsAsSet
    | _ => pure ()
    pending := pending ++ deps.toArray
  unless actualAxioms.all (fun a => #["propext","Classical.choice","Quot.sound"].contains a) do
    throwError "unexpected actual recursive axiom {actualAxioms}"
  let mut providerRows : Array Json := #[]
  for m in env.header.moduleNames do
    let object ← findOLean m
    providerRows := providerRows.push (Json.mkObj [("module",toJson m.toString),
      ("object",toJson object.toString)])
  liftIO <| IO.FS.writeFile "../logs/ORIGINAL_A5_FULL_SELECTED_OBJECTS_v475.json"
    (Json.arr providerRows).pretty
  liftIO <| IO.FS.writeFile "../logs/ORIGINAL_A5_FULL_ACTUAL_CLOSURE_v475.json"
    (Json.mkObj [("status",toJson "PASS_FULL_ORIGINAL_A5"),
      ("root_count",toJson roots.size),("actual_closure_count",toJson seen.size),
      ("kernel_checked_actual_values",toJson true),("original_proof_credit",toJson true),
      ("constructor_field_expansion",toJson true),("recursor_expansion",toJson true),
      ("actual_recursive_axioms",toJson actualAxioms),
      ("dependencies",Json.arr rows)]).pretty
