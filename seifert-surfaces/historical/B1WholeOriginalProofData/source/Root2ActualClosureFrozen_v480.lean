import OriginalB1_v468
import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array Name := #[`SeifertSurfaces.OriginalEndpoints.original_prop57_tangencies,
    `SeifertSurfaces.OriginalEndpoints.B1_original]
  for root in roots do
    let some ci := env.find? root | throwError "missing original root {root}"
    let some value := ci.value? (allowOpaque := true) | throwError "missing root proof {root}"
    liftTermElabM <| checkWithKernel value
  let mut initial : NameSet := {}
  for root in roots do
    initial := initial.insert root
  let mut recursorsByInductive : Std.HashMap Name (Array Name) := {}
  for data in env.header.moduleData do
    for n in data.constNames do
      if let some (.recInfo val) := env.find? n then
        for ind in val.all do
          recursorsByInductive := recursorsByInductive.insert ind
            ((recursorsByInductive[ind]?.getD #[]).push n)
  let mut pending := initial.toArray
  let mut seen : NameSet := {}
  let mut enqueued : NameSet := initial
  let mut axioms : NameSet := {}
  let mut modules : NameSet := {}
  let mut missing : Array String := #[]
  let mut edges := pending.size
  let mut sorryUsers : Array String := #[]
  let mut index := 0
  while index < pending.size do
    let n := pending[index]!
    index := index + 1
    if seen.contains n then continue
    seen := seen.insert n

    let some ci := env.find? n | missing := missing.push n.toString; continue
    if let some mi := env.getModuleIdxFor? n then
      let mod := env.header.modules[mi.toNat]!.module
      modules := modules.insert mod
    let mut deps := ci.type.getUsedConstantsAsSet
    match ci with
    | .axiomInfo _ => axioms := axioms.insert n
    | .thmInfo v => deps := deps.merge v.value.getUsedConstantsAsSet
    | .defnInfo v => deps := deps.merge v.value.getUsedConstantsAsSet
    | .opaqueInfo v => deps := deps.merge v.value.getUsedConstantsAsSet
    | .ctorInfo v => deps := deps.insert v.induct
    | .inductInfo v =>
      for m in v.all ++ v.ctors do deps := deps.insert m
      for m in recursorsByInductive[n]?.getD #[] do deps := deps.insert m
      if let some st := getStructureInfo? env n then
        for f in st.fieldInfo do deps := deps.insert f.projFn
        for p in st.parentInfo do deps := deps.insert p.structName |>.insert p.projFn
    | .recInfo v =>
      for m in v.all do deps := deps.insert m
      for rule in v.rules do
        deps := deps.insert rule.ctor
        deps := deps.merge rule.rhs.getUsedConstantsAsSet
    | .quotInfo _ => pure ()
    if deps.contains `sorryAx then sorryUsers := sorryUsers.push n.toString
    edges := edges + deps.toArray.size
    for dep in deps.toArray do
      unless enqueued.contains dep do
        enqueued := enqueued.insert dep
        pending := pending.push dep

  let bad := axioms.toArray.filter fun n => n != `propext && n != `Classical.choice && n != `Quot.sound

  unless missing.isEmpty && bad.isEmpty do throwError m!"whole frozen closure rejected {missing}: {bad}"

  liftIO <| IO.FS.writeFile "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/WHOLE_ORIGINAL_RELEASE_v480/logs/ROOT2_ACTUAL_FULL_CLOSURE_FROZEN_v480.json" (Json.mkObj [
    ("status",toJson (if bad.isEmpty && missing.isEmpty then "PASS" else "UNPAID_SOURCE_OBLIGATIONS")),
    ("direct_sorry_users",toJson sorryUsers),
    ("original_type_body_proved",toJson bad.isEmpty),("selected_provider_roots",toJson (roots.map Name.toString)),
    ("partial_closure_complete",toJson true),("declarations",toJson seen.toArray.size),
    ("direct_edges",toJson edges),("modules",toJson modules.toArray.size),("module_names",toJson (modules.toArray.map Name.toString)),
    ("missing",toJson missing),("axioms",toJson (axioms.toArray.map Name.toString)),
    ("unexpected_axioms",toJson (bad.map Name.toString)),
    ("proof_definition_opaque_values_recursor_rules_and_inductives_expanded",toJson true),
    ("caller_cycle",toJson false),("actual_unsanitized_values",toJson true),
    ("names",toJson (seen.toArray.map Name.toString)),("unpaid_dependencies",toJson sorryUsers.size)]).pretty
  logInfo m!"Original roots actual closure: {seen.toArray.size} declarations; axioms {bad}; direct source gaps {sorryUsers}"
