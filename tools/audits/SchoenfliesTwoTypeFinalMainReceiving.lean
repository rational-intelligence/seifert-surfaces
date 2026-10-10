import MainTheorems
import ExactPaidCodec
import Lean
open Lean Elab Command Meta ExactPaidSource
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
run_cmd do
 unless !debug.skipKernelTC.get (← getOptions) do throwError "kernel checking disabled"
 let text ← liftIO <| IO.FS.readFile "tools/fixtures/SCHOENFLIES_EXACT_EXPECTED_TWO_ROWS.json"
 let rows ← ofExcept <| (← ofExcept <| Json.parse text).getArr?
 let mut output : Array Json := #[]
 for row in rows do
  let n ← ofExcept <| nameFromJson (← ofExcept <| row.getObjVal? "name")
  let lpj ← ofExcept <| row.getObjValAs? (α := Array Json) "levels"
  let lp ← ofExcept <| lpj.toList.mapM nameFromJson
  let ty ← ofExcept <| exprFromJson (← ofExcept <| row.getObjVal? "type")
  let env := (← getEnv).setExporting false
  let some ci := env.find? n | throwError "current theorem missing {n}"
  unless ci matches .thmInfo _ do throwError "current declaration not theorem"
  let defeq := Kernel.isDefEqGuarded env {} ty ci.type
  let oldPretty ← liftTermElabM <| ppExpr ty
  let newPretty ← liftTermElabM <| ppExpr ci.type
  let mut fields := [("name",toJson n.toString),("old_levels",toJson (lp.map nameJson)),("current_levels",toJson (ci.levelParams.map nameJson)),("old_type",exprJson ty),("current_type",exprJson ci.type),("old_pretty",toJson oldPretty.pretty),("current_pretty",toJson newPretty.pretty),("kernel_isDefEq",toJson defeq)]
  logInfo m!"OLD {n}: {oldPretty}"
  logInfo m!"CURRENT {n}: {newPretty}"
  let owner := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i.toNat]!.toString | none => "LOCAL"
  fields := fields ++ [("actual_owner",toJson owner)]
  let cert := Name.mkSimple ("AuditExactOldType_" ++ n.toString.replace "." "_")
  try
   liftCoreM <| addDecl <| .thmDecl {name := cert,levelParams := lp,type := ty,value := mkConst n (lp.map Level.param)}
   logInfo m!"PASS normal synchronous kernel current proof against exact entire old type {n}"
   fields := fields ++ [("kernel_exact_old_type_current_proof",toJson "PASS")]
  catch ex =>
   logInfo m!"FAIL exact old type/current proof {n}: {ex.toMessageData}"
   fields := fields ++ [("kernel_exact_old_type_current_proof",toJson "FAIL"),("failure",toJson (← ex.toMessageData.toString))]
  output := output.push <| Json.mkObj fields
 liftIO <| IO.FS.writeFile "tools/verification-reports/SCHOENFLIES_TWO_TYPE_RECEIVING_COMPARISON.json" (Json.pretty (toJson output))

#print axioms AuditExactOldType_Schoenflies_Plane_exists_closedSquare_of_finite
#print axioms AuditExactOldType_Schoenflies_Plane_isOpen_compl_of_finite_isCompact
