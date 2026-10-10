import MainTheorems
import ExactPaidCodec
import Lean
open Lean Elab Command Meta ExactPaidSource
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

partial def isOpenFunction (e : Expr) : Except String Expr := do
 match e with
 | .lam n ty b bi => return .lam n ty (← isOpenFunction b) bi
 | _ =>
  unless e.getAppFn == mkConst `TopologicalSpace.mk [.zero] do throw "not literal topology constructor"
  let args := e.getAppArgs
  unless args.size == 5 do throw "wrong constructor arity"
  return args[1]!

def kernelEqualityCheck (env : Environment) (ty lhs rhs : Expr) : Except Kernel.Exception Expr := do
 let target := mkApp3 (mkConst `Eq [.succ .zero]) ty lhs rhs
 let refl := mkApp2 (mkConst `Eq.refl [.succ .zero]) ty lhs
 Kernel.check env {} (.letE `auditEquality target refl (.bvar 0) false)

run_cmd do
 unless !debug.skipKernelTC.get (← getOptions) && !Elab.async.get (← getOptions) do throwError "kernel audit options unsafe"
 let input := "tools/fixtures/COMMON_B_TOPOLOGY_APPROVED_LITERAL_FIXTURE.json"
 let j ← ofExcept <| Json.parse (← liftIO <| IO.FS.readFile input)
 let oldType ← ofExcept <| j.getObjVal? "old_type" >>= exprFromJson
 let oldExpanded ← ofExcept <| j.getObjVal? "old_topology_expanded" >>= exprFromJson
 let oldData ← ofExcept <| j.getObjVal? "old_data" >>= exprFromJson
 let env := (← getEnv).setExporting false
 let n := `SeifertSurfaces.Foundations.SmoothExterior.instTopologicalSpaceCarrier
 let some fresh := env.find? n | throwError "fresh topology absent"
 let some freshValue := fresh.value? | throwError "fresh topology value absent"
 unless Expr.equal oldType fresh.type && ExprStructEq.mk oldType == ExprStructEq.mk fresh.type do throwError "topology full type raw drift"
 let newData ← ofExcept <| isOpenFunction freshValue
 unless Expr.equal oldData newData && ExprStructEq.mk oldData == ExprStructEq.mk newData do throwError "IsOpen data raw drift"
 let _ ← ofExcept <| (Kernel.check env {} oldExpanded).mapError (fun _ => "normal kernel old expanded value check failed")
 let dataType ← ofExcept <| (Kernel.check env {} oldData).mapError (fun _ => "normal kernel IsOpen data check failed")
 let _ ← ofExcept <| (kernelEqualityCheck env oldType oldExpanded (mkConst n)).mapError (fun _ => "normal kernel topology closed equality failed")
 let _ ← ofExcept <| (kernelEqualityCheck env dataType oldData newData).mapError (fun _ => "normal kernel IsOpen closed equality failed")
 logInfo "PASS receiving topology literal normal-kernel closed equality; full topology type and IsOpen data raw identical; four original raw failures preserved separately"
