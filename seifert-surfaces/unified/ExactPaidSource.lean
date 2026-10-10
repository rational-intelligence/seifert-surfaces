import ExactPaidCodec
open Lean Elab Command
namespace ExactPaidSource
private def names (j : Json) : Except String (List Name) := do
 (← j.getArr?).toList.mapM nameFromJson
private def field (j : Json) (k : String) : Except String Json := j.getObjVal? k
private def expr (j : Json) (k : String) : Except String Expr := do exprFromJson (← field j k)
private def decode (j : Json) : Except String Declaration := do
 let kind ← j.getObjValAs? (α := String) "kind"
 let n ← nameFromJson (← field j "name")
 let lp ← names (← field j "levels")
 let ty ← expr j "type"
 match kind with
 | "def" =>
  let v ← expr j "value"
  let all ← names (← field j "all")
  let hj ← field j "hints"
  let ha ← hj.getArr?
  let hints ← match ← ha[0]!.getStr? with
   | "opaque" => pure ReducibilityHints.opaque
   | "abbrev" => pure ReducibilityHints.abbrev
   | "regular" => pure (ReducibilityHints.regular (UInt32.ofNat (← fromJson? ha[1]!)))
   | _ => throw "invalid kernel hints"
  return .defnDecl { name := n, levelParams := lp, type := ty, value := v, hints := hints, safety := .safe, all := all }
 | "thm" => return .thmDecl { name := n, levelParams := lp, type := ty, value := (← expr j "value"), all := (← names (← field j "all")) }
 | "opaque" => return .opaqueDecl { name := n, levelParams := lp, type := ty, value := (← expr j "value"), isUnsafe := false, all := (← names (← field j "all")) }
 | "induct" =>
  let np ← j.getObjValAs? (α := Nat) "numParams"
  let mut types : List InductiveType := []
  for t in (← (← field j "types").getArr?) do
   let mut ctors : List Constructor := []
   for c in (← (← field t "ctors").getArr?) do
    ctors := ctors ++ [{ name := (← nameFromJson (← field c "name")), type := (← expr c "type") }]
   types := types ++ [{ name := (← nameFromJson (← field t "name")), type := (← expr t "type"), ctors := ctors }]
  return .inductDecl lp np types false
 | _ => throw "unsupported declaration; axioms are forbidden"
/-- Import exact closed paid terms as Lean source and submit every missing declaration
    to the normal Lean kernel. No filesystem or donor environment is accessed. -/
def addJSON (text : String) : CommandElabM Unit := do
 if debug.skipKernelTC.get (← getOptions) then throwError "Kernel checking cannot be disabled"
 if Elab.async.get (← getOptions) then throwError "Exact paid source requires Elab.async=false"
 let j ← ofExcept (Json.parse text)
 let decl ← ofExcept (decode j)
 let name ← ofExcept <| nameFromJson (← ofExcept (field j "name"))
 let env := (← getEnv).setExporting false
 if let some ci := env.find? name then
  let metadataSame : Bool := match ci,decl with
   | .defnInfo a,.defnDecl b => a.name == b.name && a.levelParams == b.levelParams && a.hints == b.hints && a.safety == b.safety && a.all == b.all
   | .thmInfo a,.thmDecl b => a.name == b.name && a.levelParams == b.levelParams && a.all == b.all
   | .opaqueInfo a,.opaqueDecl b => a.name == b.name && a.levelParams == b.levelParams && a.isUnsafe == b.isUnsafe && a.all == b.all
   | .inductInfo a,.inductDecl lp np ts unsafeFlag => a.levelParams == lp && a.numParams == np && a.all == ts.map (·.name) && a.isUnsafe == unsafeFlag
   | _,_ => false
  unless metadataSame do throwError "Conflicting paid declaration kind/kernel metadata: {name}"
  if let .inductDecl lp np ts unsafeFlag := decl then
   for t in ts do
    let some (.inductInfo i) := env.find? t.name | throwError "Missing existing inductive member {t.name}"
    unless i.levelParams == lp && i.numParams == np && i.all == ts.map (·.name) && i.ctors == t.ctors.map (·.name) && i.isUnsafe == unsafeFlag && Expr.equal i.type t.type && ExprStructEq.mk i.type == ExprStructEq.mk t.type do
     throwError "Conflicting existing inductive shape {t.name}"
    for c in t.ctors do
     let some (.ctorInfo actual) := env.find? c.name | throwError "Missing existing constructor {c.name}"
     unless actual.induct == t.name && actual.levelParams == lp && actual.numParams == np && Expr.equal actual.type c.type && ExprStructEq.mk actual.type == ExprStructEq.mk c.type do
      throwError "Conflicting existing constructor shape {c.name}"
   -- Existing inductive acceptance requires an independent full raw CI/recursor audit.
   -- Refuse here rather than silently validating less than the kernel family.
   throwError "Existing inductive requires independent full constructor/recursor equality audit: {name}"
  let expectedType ← ofExcept (expr j "type")
  let expectedLevels ← ofExcept (names (← ofExcept (field j "levels")))
  unless ci.levelParams == expectedLevels && Expr.equal ci.type expectedType && ExprStructEq.mk ci.type == ExprStructEq.mk expectedType do
   throwError "Conflicting existing paid declaration type: {name}"
  if let .ok expectedValue := expr j "value" then
   let some v := ci.value? (allowOpaque := true) | throwError "Existing paid declaration has no value: {name}"
   unless Expr.equal v expectedValue && ExprStructEq.mk v == ExprStructEq.mk expectedValue do
    throwError "Conflicting existing paid declaration value: {name}"
 else
  liftCoreM <| addDecl decl
  let actual := (← getEnv).setExporting false
  let some ci := actual.find? name | throwError "Missing kernel checked declaration: {name}"
  let ty ← ofExcept (expr j "type")
  unless Expr.equal ci.type ty && ExprStructEq.mk ci.type == ExprStructEq.mk ty do
   throwError "Kernel replay changed type: {name}"
  if let .ok v := expr j "value" then
   let some av := ci.value? (allowOpaque := true) | throwError "Missing checked value: {name}"
   unless Expr.equal av v && ExprStructEq.mk av == ExprStructEq.mk v do
    throwError "Kernel replay changed value: {name}"
end ExactPaidSource

open Lean Elab Tactic Meta
namespace ExactPaidSource
/-- Validate original full raw types and operative definitions in the receiving environment. -/
def guardJSON (text : String) : CommandElabM Unit := do
 let j ← ofExcept (Json.parse text)
 let n ← ofExcept (nameFromJson (← ofExcept (j.getObjVal? "name")))
 let lpJSON ← ofExcept (j.getObjValAs? (α := Array Json) "levels")
 let lp ← ofExcept (lpJSON.toList.mapM nameFromJson)
 let ty ← ofExcept (exprFromJson (← ofExcept (j.getObjVal? "type")))
 let some ci := ((← getEnv).setExporting false).find? n | throwError "Original type guard missing {n}"
 unless ci.levelParams == lp && Expr.equal ci.type ty && ExprStructEq.mk ci.type == ExprStructEq.mk ty do
  throwError "Original full raw type drift {n}"
 if let .ok vJSON := j.getObjVal? "value" then
  let v ← ofExcept (exprFromJson vJSON)
  let some actual := ci.value? (allowOpaque := true) | throwError "Original operative value absent {n}"
  unless Expr.equal actual v && ExprStructEq.mk actual == ExprStructEq.mk v do
   throwError "Original operative definition drift {n}"
/-- Reuse a closed captured proof under the unchanged source declaration header. -/
elab "exact_paid_term " payload:str : tactic => do
 if debug.skipKernelTC.get (← getOptions) then throwError "Kernel checking cannot be disabled"
 let j ← ofExcept (Json.parse payload.getString)
 let p ← ofExcept (exprFromJson (← ofExcept (j.getObjVal? "value")))
 let paramsJSON ← ofExcept (j.getObjValAs? (α := Array Json) "levels")
 let params ← ofExcept (paramsJSON.toList.mapM nameFromJson)
 let levels ← params.mapM fun _ => mkFreshLevelMVar
 let p := p.instantiateLevelParams params levels
 let goal ← getMainGoal
 let goals ← goal.withContext <| goal.apply p
 for g in goals do
  unless ← g.assumptionCore do throwError "Captured paid proof left unmatched source hypothesis"
 replaceMainGoal []
end ExactPaidSource
