import B3NativeCoefficientReplayV481
import Lean

/- Replays exactly the native B3 coefficient producer in the Section 5 context.
Every declaration in the transitive closure is checked for literal type/value
equality and every new declaration is checked by the Lean kernel. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
  let old ← liftIO do
    let saved ← searchPathRef.get
    let .ok j := Json.parse (← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_original_section5_approved26_v480/migration_v480/donor_b3_analytic/environment.json")
      | throw <| IO.userError "donor environment JSON"
    let .ok paths := j.getObjValAs? (Array String) "LEAN_PATH"
      | throw <| IO.userError "donor environment paths"
    searchPathRef.set (paths.toList.map System.FilePath.mk)
    try
      enableInitializersExecution
      importModules #[{module := `B3InteriorAnalyticConclusionV480}] {} 0
        (loadExts := true) (leakEnv := true)
    finally
      searchPathRef.set saved
  let roots := #[`SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480.original_pair_graph_full_analytic_conclusion]
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut j := 0
  while j < todo.size do
    let n := todo[j]!
    j := j + 1
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := old.find? n | throwError "missing producer constant {n}"
    if n == `sorryAx then throwError "unpaid producer constant"
    if ci.isAxiom && !#[`propext,`Classical.choice,`Quot.sound].contains n then
      throwError "nonbase producer axiom {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
    match ci with
    | .inductInfo d => todo := todo ++ d.all.toArray ++ d.ctors.toArray
    | .ctorInfo d => todo := todo.push d.induct
    | .recInfo d =>
      todo := todo ++ d.all.toArray
      for r in d.rules do todo := todo ++ r.rhs.getUsedConstants |>.push r.ctor
    | _ => pure ()
  let initial := (← getEnv).setExporting false
  let mut pending := seen.toArray.filter (fun n => (initial.find? n).isNone)
  let added := pending.size
  while !pending.isEmpty do
    let mut next := #[]
    let mut progress := false
    for n in pending do
      let env := (← getEnv).setExporting false
      if (env.find? n).isSome then continue
      let some ci := old.find? n | throwError "missing replay constant {n}"
      match ci with
      | .inductInfo d =>
        let mut types : List InductiveType := []
        let mut deps := ci.type.getUsedConstants
        for t in d.all do
          let some (.inductInfo td) := old.find? t | throwError "inductive group missing {t}"
          let mut ctors : List Constructor := []
          deps := deps ++ td.type.getUsedConstants
          for c in td.ctors do
            let some cc := old.find? c | throwError "constructor missing {c}"
            ctors := ctors ++ [{name := c, type := cc.type}]
            deps := deps ++ cc.type.getUsedConstants
          types := types ++ [{name := t, type := td.type, ctors := ctors}]
        if deps.any (fun m => !d.all.contains m && (env.find? m).isNone) then
          next := next.push n; continue
        if d.isUnsafe then throwError "unsafe inductive producer {n}"
        setEnv <| Environment.ofKernelEnv (← getEnv).toKernelEnv
        liftCoreM <| addDecl (.inductDecl d.levelParams d.numParams types false)
      | .ctorInfo _ | .recInfo _ => next := next.push n; continue
      | _ =>
        let some v := ci.value? (allowOpaque := true) | throwError "missing replay value {n}"
        let deps := ci.type.getUsedConstants ++ v.getUsedConstants
        if deps.any (fun m => (env.find? m).isNone) then next := next.push n; continue
        match ci with
        | .defnInfo d =>
          unless d.safety == .safe do throwError "unsafe definition {n}"
          setEnv <| Environment.ofKernelEnv (← getEnv).toKernelEnv
          liftCoreM <| addDecl (.defnDecl d)
        | .thmInfo d =>
          setEnv <| Environment.ofKernelEnv (← getEnv).toKernelEnv
          liftCoreM <| addDecl (.thmDecl d)
        | .opaqueInfo d =>
          if d.isUnsafe then throwError "unsafe opaque {n}"
          setEnv <| Environment.ofKernelEnv (← getEnv).toKernelEnv
          liftCoreM <| addDecl (.opaqueDecl d)
        | _ => throwError "unreplayable declaration {n}"
      progress := true
    unless progress || next.isEmpty do throwError "replay dependency stall {next}"
    pending := next
  let fresh := (← getEnv).setExporting false
  for n in seen.toArray do
    let some a := old.find? n | throwError "lost original {n}"
    let some b := fresh.find? n | throwError "lost replay {n}"
    unless a == b && a.levelParams == b.levelParams &&
        Expr.equal a.type b.type && ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
        (match a.value? (allowOpaque := true), b.value? (allowOpaque := true) with
         | some x, some y => Expr.equal x y && ExprStructEq.mk x == ExprStructEq.mk y
         | none, none => true
         | _, _ => false) do throwError "literal native type/value mismatch {n}"
    match a,b with
    | .recInfo x,.recInfo y =>
      unless (x.rules.zip y.rules).all (fun (p,q) =>
        Expr.equal p.rhs q.rhs && ExprStructEq.mk p.rhs == ExprStructEq.mk q.rhs) do
        throwError "literal recursor rule mismatch {n}"
    | _,_ => pure ()
  for n in roots do
    let ax ← liftCoreM <| collectAxioms n
    unless ax.all (#[`propext,`Classical.choice,`Quot.sound].contains ·) do
      throwError "unexpected root axioms {ax}"
  logInfo m!"PAID_B3_ANALYTIC_EXACT_CLOSURE_REPLAY_PASS closure={seen.size} replayed={added} base3"
