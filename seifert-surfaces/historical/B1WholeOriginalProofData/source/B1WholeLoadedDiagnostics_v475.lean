import Lean
open Lean
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def literalConstantEqual (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type &&
    match a.value? (allowOpaque:=true), b.value? (allowOpaque:=true) with
    | some av, some bv => av.equal bv
    | none, none => true
    | _, _ => false

def main (args : List String) : IO Unit := do
  let moduleName := (args.headD "OriginalB1_v468").toName
  let env ← importModules #[{module:=moduleName}] {}
  let mut rows : Array Json := #[]
  let mut okay := true
  for n in env.header.moduleNames do
    if n.getRoot == `Schoenflies then
      throw <| IO.userError s!"Forbidden ordinary Schoenflies module loaded: {n}"
    let p ← findOLean n
    if p.toString.startsWith "/home/caoyichuan/.elan/" ||
        p.toString.contains ".lake/packages/" then
      continue
    unless p.toString.startsWith "/home/caoyichuan/test/seifert-surfaces/target/" ||
        p.toString.startsWith "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/generate_B1_tangency_and_original_v468/" do
      throw <| IO.userError s!"Unpinned loaded object root: {p}"
    let (md,_) ← readModuleData p
    let mut equal := true
    let mut differences : Array Json := #[]
    for a in md.constants do
      match env.find? a.name with
      | some b =>
        let good := literalConstantEqual a b
        equal := equal && good
        if !good then differences := differences.push <| Json.mkObj [
          ("name",toJson a.name.toString),("level_parameters_equal",toJson (a.levelParams==b.levelParams)),
          ("type_literal_equal",toJson (a.type.equal b.type)),
          ("value_literal_equal",toJson (match a.value? (allowOpaque:=true),b.value? (allowOpaque:=true) with
            | some av,some bv => av.equal bv | none,none => true | _,_ => false))]
      | none => equal := false
    okay := okay && equal
    rows := rows.push <| Json.mkObj [("module",toJson n.toString),
      ("path",toJson p.toString),("constant_count",toJson md.constants.size),
      ("all_saved_constants_literal_equal_actual_loaded",toJson equal),
      ("differences",Json.arr differences),
      ("imports",toJson (md.imports.map (fun i=>i.module.toString)))]
  IO.println <| (Json.mkObj [("okay",toJson okay),
    ("method",toJson "Every project saved ConstantInfo type, levels and operative value compared to actual loaded environment using Expr.equal; no normalization or rewritten module headers"),
    ("modules_count",toJson rows.size),("modules",Json.arr rows)]).pretty
  unless okay do throw <| IO.userError "Loaded native inventory mismatch"
