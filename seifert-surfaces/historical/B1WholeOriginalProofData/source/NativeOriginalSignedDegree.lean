import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Topology.MetricSpace.HausdorffDimension
import B1L1DirectWeakLower
import NativeOriginalUnsignedPackage
import VM03CountGeometry
import DifferentialGeometry.External.DeGiorgi.BallExtensionEstimates
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import NativeSignedMissingEquation_v465
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
 let source := System.FilePath.mk (← getFileName)
 let (data,_) ← liftIO <| readModuleData (source.parent.getD "." / "ProofData" / "exact_original_signed_degree.olean")
 let mut all : Std.HashMap Name ConstantInfo := {}
 for ci in data.constants do all := all.insert ci.name ci
 let roots := #[(Name.num `_private.NativeOriginalSignedDegree 0).str "native_original_signed_weighted_degree"]
 let rawEq (a b : ConstantInfo) : Bool :=
  a == b && a.levelParams == b.levelParams && Expr.equal a.type b.type && ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
  (match a.value? (allowOpaque := true),b.value? (allowOpaque := true) with
   | some x,some y => Expr.equal x y && ExprStructEq.mk x == ExprStructEq.mk y
   | none,none => true
   | _,_ => false) &&
  (match a,b with
   | .recInfo x,.recInfo y => x.rules.length == y.rules.length && (x.rules.zip y.rules).all (fun (r,s) => r.ctor == s.ctor && r.nfields == s.nfields && Expr.equal r.rhs s.rhs && ExprStructEq.mk r.rhs == ExprStructEq.mk s.rhs)
   | .recInfo _,_ => false
   | _,.recInfo _ => false
   | _,_ => true)
 let mut pending := data.constants
 while !pending.isEmpty do
  let mut next := #[]; let mut progress := false
  for ci in pending do
   let env := (← getEnv).setExporting false
   if let some b := env.find? ci.name then
    unless rawEq ci b do throwError "existing paid support drift {ci.name}"
    progress := true
    continue
   match ci with
   | .inductInfo iv =>
    let mut types : List InductiveType := []
    let mut family : NameSet := {}
    for n in iv.all do
     let some (.inductInfo v) := all[n]? | throwError "paid inductive member absent {n}"
     family := family.insert n
     for cn in v.ctors do family := family.insert cn
    let mut deps : NameSet := {}
    for n in family.toArray do
     let some x := all[n]? | throwError "paid family member absent {n}"
     deps := deps.union x.type.getUsedConstantsAsSet
    if deps.toArray.any (fun n => !family.contains n && (env.find? n).isNone) then
     next := next.push ci
     continue
    for n in iv.all do
     let some (.inductInfo v) := all[n]? | throwError "family missing"
     let mut ctors : List Constructor := []
     for cn in v.ctors do
      let some (.ctorInfo c) := all[cn]? | throwError "constructor missing"
      ctors := ctors ++ [{name:=cn,type:=c.type}]
     types := types ++ [{name:=n,type:=v.type,ctors:=ctors}]
    liftCoreM <| addDecl (.inductDecl iv.levelParams iv.numParams types iv.isUnsafe)
    for n in family.toArray do
     let some x := all[n]? | throwError "family missing"
     let some b := ((← getEnv).setExporting false).find? n | throwError "generated family missing"
     unless rawEq x b do throwError "generated paid family drift {n}"
    progress := true
   | .ctorInfo _ => next := next.push ci
   | .recInfo _ => next := next.push ci
   | _ =>
    let some value := ci.value? (allowOpaque := true) | throwError "unreplayable foreign primitive {ci.name}"
    let deps := ci.type.getUsedConstantsAsSet.union value.getUsedConstantsAsSet
    if deps.toArray.any (fun n => (env.find? n).isNone) then next := next.push ci; continue
    match ci with
    | .defnInfo d => liftCoreM <| addDecl (.defnDecl d)
    | .thmInfo d => liftCoreM <| addDecl (.thmDecl d)
    | .opaqueInfo d => liftCoreM <| addDecl (.opaqueDecl d)
    | _ => throwError "unexpected paid declaration kind {ci.name}"
    let some b := ((← getEnv).setExporting false).find? ci.name | throwError "paid declaration not stored"
    unless rawEq ci b do throwError "stored paid type/value drift {ci.name}"
    progress := true
  unless progress do throwError "unavailable paid native dependencies {next.map ConstantInfo.name}"
  pending := next
 for n in roots do
  let some ci := ((← getEnv).setExporting false).find? n | throwError "paid provider root absent"
  let some v := ci.value? (allowOpaque := true) | throwError "paid provider body absent"
  liftTermElabM <| Lean.Meta.checkWithKernel v
