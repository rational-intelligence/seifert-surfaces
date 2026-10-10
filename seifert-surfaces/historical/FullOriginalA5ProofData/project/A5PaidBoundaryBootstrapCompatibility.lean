import A5NativeBoundaryStraightenedMetricData
import A5MetricGraphInteriorFromImageCover
import A5NativeSmoothHalfdiscImage
import Lean

/- Load the sealed full bootstrap separately, kernel replay its missing closure,
then compare every literal ConstantInfo, type and value in this native consumer. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
  let old ← liftIO do
    enableInitializersExecution
    importModules #[{module := `A5BoundaryBootstrapV465}] {} 0 (loadExts := true) (leakEnv := true)
  let roots := #[`SeifertSurfaces.AppendixACoordinates.BoundaryRegularity.smooth_of_C1_weak_uniformlyElliptic_dirichlet]
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
        liftCoreM <| addDecl (.inductDecl d.levelParams d.numParams types false)
      | .ctorInfo _ | .recInfo _ => next := next.push n; continue
      | _ =>
        let some v := ci.value? (allowOpaque := true) | throwError "missing replay value {n}"
        let deps := ci.type.getUsedConstants ++ v.getUsedConstants
        if deps.any (fun m => (env.find? m).isNone) then next := next.push n; continue
        match ci with
        | .defnInfo d =>
          unless d.safety == .safe do throwError "unsafe definition {n}"
          liftCoreM <| addDecl (.defnDecl d)
        | .thmInfo d => liftCoreM <| addDecl (.thmDecl d)
        | .opaqueInfo d =>
          if d.isUnsafe then throwError "unsafe opaque {n}"
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
  liftIO <| IO.FS.writeFile "../logs/FULL_BOUNDARY_BOOTSTRAP_EXACT_REPLAY_v474.json"
    (Json.mkObj [("status",toJson "PASS_LITERAL_CI_TYPE_VALUE_REPLAY"),
      ("closure",toJson seen.size),("replayed",toJson added),
      ("root",toJson roots[0]!.toString),("base_axioms",toJson #["propext","Classical.choice","Quot.sound"])]).pretty
  logInfo m!"FULL_BOUNDARY_BOOTSTRAP_EXACT_CLOSURE_REPLAY_PASS closure={seen.size} replayed={added} base3"
