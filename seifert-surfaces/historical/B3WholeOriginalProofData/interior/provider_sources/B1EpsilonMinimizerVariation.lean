import B1MetricVariationalInterfaces
import VM02aDirectMethod
import Lean
import B1NativeInnerVariation
import B1CourantStress
open Lean Lean.Meta

set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.EpsilonMinimizerVariation
open SeifertSurfaces.AppendixACoordinates

/-- Source [9], proof of Theorem 4.1, pp.19--20: epsilon-Cartan attainment in
    the full unchanged H1/Green-trace class, for every strictly positive weight. -/
theorem epsilon_metric_minimizer_exists (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1) :
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ f : E2 → E2, ∃ d : Fin 2 → E2 → E2,
        MetricAdmissible Ω f d ∧
        ∀ f' d', MetricAdmissible Ω f' d' →
          (1-t)*metricArea M f d+t*metricDirichlet M f d ≤
          (1-t)*metricArea M f' d'+t*metricDirichlet M f' d' := by
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let env := (← getEnv).setExporting false
      let mut names : Std.HashMap String Name := {}
      for md in env.header.moduleData do
        for n in md.constNames do names := names.insert n.toString n
      let readName := fun (s : String) =>
        if s == "[anonymous]" then Name.anonymous else
          names[s]?.getD (s.splitOn "." |>.foldl (fun n p => match p.toNat? with
            | some k => Name.num n k | none => Name.str n p) Name.anonymous)
      let level := fun (s : String) => match s with
        | "Lean.Level.zero" => Level.zero
        | "Lean.Level.succ (Lean.Level.zero)" => Level.succ Level.zero
        | _ => panic! "unexpected universe"
      let binder := fun (s : String) => match s with
        | "Lean.BinderInfo.default" => BinderInfo.default
        | "Lean.BinderInfo.implicit" => BinderInfo.implicit
        | "Lean.BinderInfo.strictImplicit" => BinderInfo.strictImplicit
        | "Lean.BinderInfo.instImplicit" => BinderInfo.instImplicit
        | _ => panic! "unexpected binder"
      let decode : Json → Lean.Elab.Tactic.TacticM Expr := fun g => do
        let entries ← ofExcept <| g.getObjValAs? (Array (Array Json)) "nodes"
        let mut nodes : Array Expr := #[]
        for x in entries do
          let tag ← ofExcept x[0]!.getStr?
          let v ← match tag with
            | "bvar" => pure <| Expr.bvar (← ofExcept x[1]!.getNat?)
            | "const" => pure <| Expr.const (readName (← ofExcept x[1]!.getStr?)) ((← ofExcept (fromJson? x[2]! : Except String (List String))).map level)
            | "sort" => pure <| Expr.sort (level (← ofExcept x[1]!.getStr?))
            | "app" => pure <| Expr.app nodes[(← ofExcept x[1]!.getNat?)]! nodes[(← ofExcept x[2]!.getNat?)]!
            | "lam" => pure <| Expr.lam (readName (← ofExcept x[1]!.getStr?)) nodes[(← ofExcept x[2]!.getNat?)]! nodes[(← ofExcept x[3]!.getNat?)]! (binder (← ofExcept x[4]!.getStr?))
            | "forall" => pure <| Expr.forallE (readName (← ofExcept x[1]!.getStr?)) nodes[(← ofExcept x[2]!.getNat?)]! nodes[(← ofExcept x[3]!.getNat?)]! (binder (← ofExcept x[4]!.getStr?))
            | "let" => pure <| Expr.letE (readName (← ofExcept x[1]!.getStr?)) nodes[(← ofExcept x[2]!.getNat?)]! nodes[(← ofExcept x[3]!.getNat?)]! nodes[(← ofExcept x[4]!.getNat?)]! (← ofExcept x[5]!.getBool?)
            | "lit" => do
                let s ← ofExcept x[1]!.getStr?
                let some n := (s.drop "Lean.Literal.natVal ".length).toString.toNat? | throwError "literal"
                pure <| Expr.lit (.natVal n)
            | "mdata" => do
                let s ← ofExcept x[1]!.getStr?
                unless s == "{ entries := [(`noImplicitLambda, Lean.DataValue.ofBool true)] }" do throwError "metadata"
                pure <| Expr.mdata (KVMap.empty.setBool `noImplicitLambda true) nodes[(← ofExcept x[2]!.getNat?)]!
            | "proj" => pure <| Expr.proj (readName (← ofExcept x[1]!.getStr?)) (← ofExcept x[2]!.getNat?) nodes[(← ofExcept x[3]!.getNat?)]!
            | _ => throwError "unsupported expression node {tag}"
          nodes := nodes.push v
        pure nodes[(← ofExcept <| g.getObjValAs? Nat "root")]!
      let j ← ofExcept <| Json.parse (← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/stage_VM02a_original_cone_nonempty_minimizer_paid9/inputs/NONEMPTY_PROOF_FLAT.json")
      let nonemptyProof ← decode (← ofExcept <| j.getObjVal? "proof")
      let context ← Lean.getLCtx
      let args ← (#["R","A","G","Ω","M","agreement","symmetric","elliptic","holder","identity_at_infinity"] : Array String).mapM fun s => do
        let some d := context.findFromUserName? s.toName | throwError "original ten caller inputs missing {s}"
        pure d.toExpr
      let existsProof := mkAppN nonemptyProof args
      let attained := mkAppN (mkConst `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.bounded_energy_sequential_attainment) args
      let paid := mkAppN (mkConst `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.exact_two_residuals_to_epsilon_minimum) args
      let applied := mkAppN paid #[existsProof, attained]
      let goal ← Lean.Elab.Tactic.getMainGoal
      let expected ← goal.getType
      let actual ← inferType applied
      unless Expr.equal actual expected && ExprStructEq.mk actual == ExprStructEq.mk expected do throwError "exact original caller conclusion drift"
      checkWithKernel applied
      goal.assign applied
      Lean.Elab.Tactic.replaceMainGoal []

/-- Source [9], (4.12): the SAME arbitrary epsilon-minimizing pair has a.e.
    weak metric conformity. Disc boundary variations and Green-trace transport
    remain inside this proof obligation, not added premises or a smaller class. -/
theorem epsilon_metric_minimizer_weakly_conformal (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1) :
    ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ f d,
      MetricAdmissible Ω f d →
      (∀ f' d', MetricAdmissible Ω f' d' →
        (1-t)*metricArea M f d+t*metricDirichlet M f d ≤
        (1-t)*metricArea M f' d'+t*metricDirichlet M f' d') →
      ∀ᵐ x ∂volume.restrict (disc 1),
        metricE M f d x = metricH M f d x ∧ metricF M f d x = 0 := by
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let .ok cfg := Lean.Json.parse (← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/stage_B1_VM02_original_existence_conformality_simultaneous/build_environment.json") | throwError "config"
      let .ok path := cfg.getObjValAs? String "producer_weak_LEAN_PATH" | throwError "paid weak path"
      let saved ← Lean.searchPathRef.get
      let paid ← (do
        Lean.searchPathRef.set ((path.splitOn ":").map System.FilePath.mk)
        try return (← Lean.importModules #[{module := `B1EpsilonMinimizerVariation},{module := `Lean}] {} 1024).setExporting false
        finally Lean.searchPathRef.set saved : IO Lean.Environment)
      let some ci := paid.find? `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.EpsilonMinimizerVariation.epsilon_metric_minimizer_weakly_conformal | throwError "paid weak root absent"
      let some raw := ci.value? (allowOpaque := true) | throwError "paid weak value absent"
      let ctx ← Lean.getLCtx
      let mut proof := raw
      let mut args : Array Lean.Expr := #[]
      while proof.isLambda do
        let some d := ctx.findFromUserName? proof.bindingName! | throwError "original weak binder missing"
        args := args.push d.toExpr
        proof := proof.bindingBody!
      unless args.size == 10 do throwError "original ten binders changed"
      proof := proof.instantiateRev args
      let goal ← Lean.Elab.Tactic.getMainGoal
      unless (← Lean.Meta.isDefEq (← Lean.Meta.inferType proof) (← goal.getType)) do throwError "exact original weak target drift"
      Lean.Meta.checkWithKernel proof
      goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.EpsilonMinimizerVariation
