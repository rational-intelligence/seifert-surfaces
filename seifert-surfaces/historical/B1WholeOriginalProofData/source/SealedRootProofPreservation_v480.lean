import Lean
open Lean
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def main : IO Unit := do
  let env ← importModules #[{module:=`OriginalB1_v468}] {}
  let mut rows : Array Json := #[]
  for (module,name) in #[(`OriginalB1_v468,`SeifertSurfaces.OriginalEndpoints.B1_original),
      (`B1ActualGeometry_v468,`SeifertSurfaces.OriginalEndpoints.original_prop57_tangencies)] do
    let oldPath := System.FilePath.mk ("/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/objects/" ++ module.toString ++ ".olean")
    let (md,_) ← readModuleData oldPath
    let some a := md.constants.find? (fun ci=>ci.name==name) | throw <| IO.userError "sealed root absent"
    let some b := env.find? name | throw <| IO.userError "clean root absent"
    let equal := a.levelParams==b.levelParams && Expr.equal a.type b.type && ExprStructEq.mk a.type==ExprStructEq.mk b.type &&
      (match a.value? (allowOpaque:=true),b.value? (allowOpaque:=true) with
       | some av,some bv => Expr.equal av bv && ExprStructEq.mk av==ExprStructEq.mk bv
       | _,_ => false)
    rows := rows.push <| Json.mkObj [("name",toJson name.toString),("sealed_object",toJson oldPath.toString),
      ("type_levels_proof_literal_unchanged",toJson equal)]
    unless equal do throw <| IO.userError "sealed root raw proof drift"
  IO.println <| (Json.mkObj [("okay",toJson true),("roots",Json.arr rows)]).pretty
