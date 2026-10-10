import B1EpsilonMinimizerVariation
import Lean
open Lean Elab Command Meta
set_option maxRecDepth 100000
set_option maxHeartbeats 0
run_cmd do
  let current := (← getEnv).setExporting false
  let .ok cfg := Json.parse (← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/prepare_B1_simultaneous_minimizer_acyclic_owner_transfer/build_environment.json") | throwError "transfer config"
  let .ok path := cfg.getObjValAs? String "capture_path" | throwError "capture path"
  let saved ← liftIO searchPathRef.get
  liftIO enableInitializersExecution
  let paid ← liftIO do
    searchPathRef.set ((path.splitOn ":").map System.FilePath.mk)
    try return (← importModules #[{module := `AnonymousSimultaneousCapture},{module := `Lean}] {} 1024 (loadExts := true)).setExporting false
    finally searchPathRef.set saved
  let root := `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.simultaneous_metric_minimizer
  unless (current.find? root).isNone do throwError "old root duplicate remains"
  let some original := paid.find? root | throwError "original protected type missing"
  let some capture := paid.find? `OwnedAnonymousSimultaneousCapture | throwError "paid caller missing"
  unless Expr.equal capture.type original.type && ExprStructEq.mk capture.type == ExprStructEq.mk original.type && capture.levelParams == original.levelParams do throwError "captured original type drift"
  let some proof := capture.value? (allowOpaque := true) | throwError "paid proof absent"
  unless !proof.hasFVar && !proof.hasMVar do throwError "captured proof is not closed"
  let generatedSupport : Array Name := #[`SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.metricAreaDensity.eq_1,`SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.metricArea.eq_1,`SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.metricDirichlet.eq_1]
  let missing := proof.getUsedConstants.filter fun n => (current.find? n).isNone
  unless missing.size == generatedSupport.size && missing.all generatedSupport.contains && generatedSupport.all missing.contains do throwError "finite generated support inventory drift {missing}"
  setEnv current
  for n in generatedSupport do
    let some ci := paid.find? n | throwError "generated equation missing {n}"
    unless ci.isTheorem do throwError "non-theorem data transfer forbidden {n}"
    let some value := ci.value? (allowOpaque := true) | throwError "generated value absent {n}"
    let env ← getEnv
    for k in ci.type.getUsedConstants ++ value.getUsedConstants do
      unless (env.find? k).isSome do throwError "new generated support dependency {k}"
    liftTermElabM <| checkWithKernel value
    liftCoreM <| addDecl (.thmDecl {name := n,levelParams := ci.levelParams,type := ci.type,value := value})
  liftTermElabM <| checkWithKernel proof
  liftCoreM <| addDecl (.thmDecl {name := root,levelParams := original.levelParams,type := original.type,value := proof})
  let actual ← getConstInfo root
  unless Expr.equal actual.type original.type && ExprStructEq.mk actual.type == ExprStructEq.mk original.type && Expr.equal (actual.value? (allowOpaque := true)).get! proof && ExprStructEq.mk (actual.value? (allowOpaque := true)).get! == ExprStructEq.mk proof do throwError "exact installation drift"
