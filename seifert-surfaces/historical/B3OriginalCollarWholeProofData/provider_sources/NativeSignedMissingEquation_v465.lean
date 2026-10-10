import B1L1DirectWeakLower
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
 let source := System.FilePath.mk (← getFileName)
 let (data,_) ← liftIO <| readModuleData (source.parent.getD "." / "ProofData" / "metric_weight_equation_donor.olean")
 let n := `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.metricWeight.eq_1
 let some (.thmInfo d) := data.constants.find? (fun c => c.name == n) | throwError "exact metricWeight equation absent"
 if ((← getEnv).setExporting false).find? n |>.isSome then throwError "expected absent generated leaf already exists"
 liftCoreM <| addDecl (.thmDecl d)
 let some b := ((← getEnv).setExporting false).find? n | throwError "generated exact leaf not stored"
 unless Expr.equal d.type b.type && ExprStructEq.mk d.type == ExprStructEq.mk b.type && (b.value? (allowOpaque:=true)).any (fun v => Expr.equal v d.value && ExprStructEq.mk v == ExprStructEq.mk d.value) && b.levelParams == d.levelParams do
  throwError "generated exact metricWeight type/value drift"
