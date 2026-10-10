import ProofTermCodec
import Lean
open Lean Elab Tactic Meta
namespace CategoryProofTooling
elab "specialized_category_proof " path:str : tactic => do
  let .ok j := Json.parse (← liftM (m := IO) <| IO.FS.readFile path.getString) | throwError "invalid proof certificate JSON"
  let .ok proofJson := j.getObjVal? "proof" | throwError "missing proof"
  let .ok p := exprFromJson proofJson | throwError "invalid closed proof expression"
  let .ok paramsJson := j.getObjValAs? (α := Array Json) "universe_parameters" | throwError "missing universes"
  let .ok params := paramsJson.toList.mapM nameFromJson | throwError "invalid universes"
  let levels ← params.mapM fun _ => mkFreshLevelMVar
  let p := p.instantiateLevelParams params levels
  let goal ← getMainGoal
  let goals ← goal.withContext <| goal.apply p
  for g in goals do
    unless ← g.assumptionCore do throwError "specialized body left an unmatched original hypothesis"
  replaceMainGoal []
end CategoryProofTooling
