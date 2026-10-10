import OriginalA5ScaffoldV464
import Lean
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
run_cmd do
  let fresh := (← getEnv).setExporting false
  let paths ← liftIO searchPathRef.get
  let frozen := System.FilePath.mk
    "/home/caoyichuan/test/seifert-surfaces/scratch/formalizer/formalize_original_A2_A5_A6_v464/objects"
  liftIO <| searchPathRef.set (frozen :: paths)
  liftIO enableInitializersExecution
  let prior ← liftIO <| importModules #[{module := `OriginalA5ScaffoldV464}]
    {} (trustLevel := 0) (loadExts := true)
  liftIO <| searchPathRef.set paths
  let root := `SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A5_original
  let some a := prior.find? root | throwError "missing approved original"
  let some b := fresh.find? root | throwError "missing consumer original"
  unless a.levelParams == b.levelParams && Expr.equal a.type b.type &&
    ExprStructEq.mk a.type == ExprStructEq.mk b.type do throwError "raw original A5 type drift"
  let mut todo := a.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut definitions := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some a := prior.find? n | throwError "missing approved native context {n}"
    let some b := fresh.find? n | throwError "missing consumer native context {n}"
    unless a.levelParams == b.levelParams && Expr.equal a.type b.type &&
      ExprStructEq.mk a.type == ExprStructEq.mk b.type do throwError "raw native type drift {n}"
    todo := todo ++ a.type.getUsedConstants
    if a.isDefinition then
      let some x := a.value? | throwError "missing approved definition {n}"
      let some y := b.value? | throwError "missing consumer definition {n}"
      unless Expr.equal x y && ExprStructEq.mk x == ExprStructEq.mk y do
        throwError "raw native definition drift {n}"
      definitions := definitions + 1
      todo := todo ++ x.getUsedConstants
    match a,b with
    | .inductInfo x,.inductInfo y =>
      unless x.numParams == y.numParams && x.numIndices == y.numIndices && x.ctors == y.ctors &&
        x.all == y.all do throwError "native inductive shape drift {n}"
      todo := todo ++ x.ctors.toArray ++ x.all.toArray
    | .recInfo x,.recInfo y =>
      unless x.rules.length == y.rules.length && (x.rules.zip y.rules).all (fun (p,q) =>
        p.ctor == q.ctor && p.nfields == q.nfields && Expr.equal p.rhs q.rhs &&
        ExprStructEq.mk p.rhs == ExprStructEq.mk q.rhs) do throwError "native recursor drift {n}"
    | _,_ => pure ()
  liftIO <| IO.FS.writeFile "../logs/ORIGINAL_A5_FULL_LITERAL_NATIVE_v475.json"
    (Json.mkObj [("status",toJson "PASS_LITERAL_ORIGINAL_TYPE_AND_NATIVE_DEFINITIONS"),
      ("type_closure",toJson seen.size),("definition_values",toJson definitions),
      ("normalization",toJson false),("original_A5_proved",toJson true)]).pretty
