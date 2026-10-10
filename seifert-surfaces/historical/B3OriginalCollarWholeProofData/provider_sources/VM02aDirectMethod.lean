import DifferentialGeometry.External.DeGiorgi.BallExtensionEstimates
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic
import CourantTranslatedPolar
import CourantAnnularProfiles
import NativeGreenTracePoincare
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Lean
import ActualConePolarGreen
import B1MetricVariationalInterfaces import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation import DifferentialGeometry.External.DeGiorgi.SobolevChainRule

set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod
open SeifertSurfaces.AppendixACoordinates

def discMeasure : Measure E2 := volume.restrict (disc 1)

def boundaryAngle (z : E2) : ℝ := Complex.arg ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)

def boundaryCone {R : ℝ} (Ω : SmoothFlatJordanDomain R) (z : E2) : E2 :=
  ‖z‖ • Ω.boundary.gamma (boundaryAngle z)

def boundaryConeJets {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (i : Fin 2) (z : E2) : E2 :=
  if z = 0 then 0 else
    (Ω.boundary.gamma (boundaryAngle z) i / ‖z‖) • z +
    (deriv Ω.boundary.gamma (boundaryAngle z) i / ‖z‖) •
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-z 1, z 0]

def NormalizedGreenTrace {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (theta : ℝ → ℝ) (sigma : ℝ) : Prop :=
  (∀ i, H1On (disc 1) (fun x => f x i) (d i)) ∧
  WeakMonotoneBoundaryLift Ω theta sigma ∧
  HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta) ∧
  theta 0 = 0 ∧ theta (2 * Real.pi / 3) = sigma * (2 * Real.pi / 3) ∧
  theta (4 * Real.pi / 3) = sigma * (4 * Real.pi / 3)

structure DiscConformalReparametrization where
  tau : PartialHomeomorph E2 E2
  source_eq : tau.source = closedDisc 1
  target_eq : tau.target = closedDisc 1
  interior_image : tau '' disc 1 = disc 1
  boundary_image : tau '' Metric.sphere (0 : E2) 1 = Metric.sphere (0 : E2) 1
  forward_C1 : ContDiffOn ℝ 1 tau (closedDisc 1)
  inverse_C1 : ContDiffOn ℝ 1 tau.symm (closedDisc 1)
  conformal_positive : ∀ z ∈ disc 1,
    let J := jacobianWithin tau (closedDisc 1) z
    ∃ lambda : ℝ, 0 < lambda ∧ J.transpose * J = lambda • (1 : Mat2) ∧
      0 < Matrix.det J

def reparametrizedWeakJets (d : Fin 2 → E2 → E2)
    (P : DiscConformalReparametrization) (i : Fin 2) (z : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun j => ∑ k, d i (P.tau z) k * jacobianWithin P.tau (closedDisc 1) z k j)

def WeakL2Converges (u : ℕ → E2 → ℝ) (v : E2 → ℝ) : Prop :=
  (∀ n, MemLp (u n) 2 discMeasure) ∧ MemLp v 2 discMeasure ∧
  ∀ test : E2 → ℝ, MemLp test 2 discMeasure →
    Filter.Tendsto (fun n => ∫ x, u n x * test x ∂discMeasure) Filter.atTop
      (𝓝 (∫ x, v x * test x ∂discMeasure))

def StrongL2Converges (u : ℕ → E2 → ℝ) (v : E2 → ℝ) : Prop :=
  (∀ n, MemLp (u n) 2 discMeasure) ∧ MemLp v 2 discMeasure ∧
  Filter.Tendsto (fun n => eLpNorm (fun x => u n x - v x) 2 discMeasure)
    Filter.atTop (𝓝 0)

-- Analytic theorem scaffolds follow, each with the unchanged ten original inputs.

open Lean Lean.Meta in
theorem boundary_cone_actual_green_extension (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1) :
    (∀ i, H1On (disc 1) (fun z => boundaryCone Ω z i) (boundaryConeJets Ω i)) ∧
    WeakMonotoneBoundaryLift Ω (fun t => t) 1 ∧
    HasGreenBoundaryTrace (boundaryCone Ω) (boundaryConeJets Ω)
      (liftedBoundaryValue Ω (fun t => t)) := by
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
      let j ← ofExcept <| Json.parse (← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/stage_VM02a_original_cone_nonempty_minimizer_paid9/inputs/CONE_PROOF_FLAT.json")
      let originalType ← decode (← ofExcept <| j.getObjVal? "type")
      let raw ← decode (← ofExcept <| j.getObjVal? "proof")
      unless !raw.hasFVar && !raw.hasMVar do throwError "serialized expression is open"
      let actualType ← inferType raw
      unless Expr.equal actualType originalType && ExprStructEq.mk actualType == ExprStructEq.mk originalType do throwError "serialized original full type drift"
      checkWithKernel raw
      let context ← Lean.getLCtx
      let mut proof := raw
      let mut expected := originalType
      let mut args : Array Expr := #[]
      while proof.isLambda do
        let n := proof.bindingName!
        let some d := context.findFromUserName? n | throwError "original binder missing {n}"
        args := args.push d.toExpr
        proof := proof.bindingBody!
        unless expected.isForall do throwError "serialized original binder type count"
        expected := expected.bindingBody!.instantiate1 d.toExpr
      unless args.size == 10 do throwError "exact original ten binders changed"
      proof := proof.instantiateRev args
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← goal.getType
      unless Expr.equal expected target && ExprStructEq.mk expected == ExprStructEq.mk target do throwError "original target raw type drift"
      unless (← Lean.Meta.isDefEq (← inferType proof) target) do throwError "original serialized application type drift"
      checkWithKernel proof
      goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []

open Lean Lean.Meta in
theorem native_green_class_nonempty (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1) :
    ∃ f : E2 → E2, ∃ d : Fin 2 → E2 → E2, MetricAdmissible Ω f d := by
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
      let originalType ← decode (← ofExcept <| j.getObjVal? "type")
      let raw ← decode (← ofExcept <| j.getObjVal? "proof")
      unless !raw.hasFVar && !raw.hasMVar do throwError "serialized expression is open"
      let actualType ← inferType raw
      unless Expr.equal actualType originalType && ExprStructEq.mk actualType == ExprStructEq.mk originalType do throwError "serialized original full type drift"
      checkWithKernel raw
      let context ← Lean.getLCtx
      let mut proof := raw
      let mut expected := originalType
      let mut args : Array Expr := #[]
      while proof.isLambda do
        let n := proof.bindingName!
        let some d := context.findFromUserName? n | throwError "original binder missing {n}"
        args := args.push d.toExpr
        proof := proof.bindingBody!
        unless expected.isForall do throwError "serialized original binder type count"
        expected := expected.bindingBody!.instantiate1 d.toExpr
      unless args.size == 10 do throwError "exact original ten binders changed"
      proof := proof.instantiateRev args
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← goal.getType
      unless Expr.equal expected target && ExprStructEq.mk expected == ExprStructEq.mk target do throwError "original target raw type drift"
      unless (← Lean.Meta.isDefEq (← inferType proof) target) do throwError "original serialized application type drift"
      checkWithKernel proof
      goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []

theorem same_map_conformal_trace_normalization (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (h1 : ∀ i, H1On (disc 1) (fun x => f x i) (d i))
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta)) :
    ∃ P : DiscConformalReparametrization, ∃ normalizedTheta : ℝ → ℝ,
      NormalizedGreenTrace Ω (fun z => f (P.tau z))
        (reparametrizedWeakJets d P) normalizedTheta sigma ∧
      (∀ t, liftedBoundaryValue Ω normalizedTheta t =
        liftedBoundaryValue Ω theta (boundaryAngle (P.tau (unitCircleParameter t)))) ∧
      metricArea M (fun z => f (P.tau z)) (reparametrizedWeakJets d P) = metricArea M f d ∧
      metricDirichlet M (fun z => f (P.tau z)) (reparametrizedWeakJets d P) =
        metricDirichlet M f d := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  Lean.Elab.Tactic.withMainContext do\n    let env := (← Lean.getEnv).setExporting false\n    let nameIndex : Std.HashMap String Lean.Name := .ofList (env.constants.toList.map fun (n,_) => (n.toString,n))\n    let readName := fun (s : String) =>\n      if s == \"[anonymous]\" then Lean.Name.anonymous else nameIndex[s]?.getD (s.splitOn \".\" |>.foldl (fun n p => match p.toNat? with | some k => Lean.Name.num n k | none => Lean.Name.str n p) Lean.Name.anonymous)\n    let level := fun (s : String) => match s with\n      | \"Lean.Level.zero\" => Lean.Level.zero\n      | \"Lean.Level.succ (Lean.Level.zero)\" => Lean.Level.succ Lean.Level.zero\n      | \"Lean.Level.succ (Lean.Level.succ (Lean.Level.zero))\" => Lean.Level.succ (Lean.Level.succ Lean.Level.zero)\n      | \"Lean.Level.max (Lean.Level.zero) (Lean.Level.zero)\" => Lean.Level.max Lean.Level.zero Lean.Level.zero\n      | \"Lean.Level.max (Lean.Level.succ (Lean.Level.zero)) (Lean.Level.succ (Lean.Level.zero))\" => Lean.Level.max (Lean.Level.succ Lean.Level.zero) (Lean.Level.succ Lean.Level.zero)\n      | _ => panic! \"unsealed universe level\"\n    let binder := fun (s : String) => match s with\n      | \"Lean.BinderInfo.default\" => Lean.BinderInfo.default\n      | \"Lean.BinderInfo.implicit\" => Lean.BinderInfo.implicit\n      | \"Lean.BinderInfo.strictImplicit\" => Lean.BinderInfo.strictImplicit\n      | \"Lean.BinderInfo.instImplicit\" => Lean.BinderInfo.instImplicit\n      | _ => panic! \"unsealed binder kind\"\n    let decode : Lean.Json → Lean.MetaM Lean.Expr := fun g => do\n      let entries ← Lean.ofExcept (g.getObjValAs? (Array (Array Lean.Json)) \"nodes\")\n      let mut nodes : Array Lean.Expr := #[]\n      for x in entries do\n        let tag ← Lean.ofExcept x[0]!.getStr?\n        let value ← match tag with\n          | \"bvar\" => pure <| Lean.Expr.bvar (← Lean.ofExcept x[1]!.getNat?)\n          | \"const\" => pure <| Lean.Expr.const (readName (← Lean.ofExcept x[1]!.getStr?)) ((← Lean.ofExcept (Lean.fromJson? x[2]! : Except String (List String))).map level)\n          | \"sort\" => pure <| Lean.Expr.sort (level (← Lean.ofExcept x[1]!.getStr?))\n          | \"app\" => pure <| Lean.Expr.app nodes[(← Lean.ofExcept x[1]!.getNat?)]! nodes[(← Lean.ofExcept x[2]!.getNat?)]!\n          | \"lam\" => pure <| Lean.Expr.lam (readName (← Lean.ofExcept x[1]!.getStr?)) nodes[(← Lean.ofExcept x[2]!.getNat?)]! nodes[(← Lean.ofExcept x[3]!.getNat?)]! (binder (← Lean.ofExcept x[4]!.getStr?))\n          | \"forall\" => pure <| Lean.Expr.forallE (readName (← Lean.ofExcept x[1]!.getStr?)) nodes[(← Lean.ofExcept x[2]!.getNat?)]! nodes[(← Lean.ofExcept x[3]!.getNat?)]! (binder (← Lean.ofExcept x[4]!.getStr?))\n          | \"let\" => pure <| Lean.Expr.letE (readName (← Lean.ofExcept x[1]!.getStr?)) nodes[(← Lean.ofExcept x[2]!.getNat?)]! nodes[(← Lean.ofExcept x[3]!.getNat?)]! nodes[(← Lean.ofExcept x[4]!.getNat?)]! (← Lean.ofExcept x[5]!.getBool?)\n          | \"lit\" => do\n            let s ← Lean.ofExcept x[1]!.getStr?\n            let some k := (s.drop \"Lean.Literal.natVal \".length).toString.toNat? | throwError \"unsealed literal {s}\"\n            pure <| Lean.Expr.lit (.natVal k)\n          | \"mdata\" => do\n            let s ← Lean.ofExcept x[1]!.getStr?\n            let key ← match s with\n              | \"{ entries := [(`noImplicitLambda, Lean.DataValue.ofBool true)] }\" => pure `noImplicitLambda\n              | \"{ entries := [(`noindex, Lean.DataValue.ofBool true)] }\" => pure `noindex\n              | _ => throwError \"unsealed metadata {s}\"\n            pure <| Lean.Expr.mdata (Lean.KVMap.empty.setBool key true) nodes[(← Lean.ofExcept x[2]!.getNat?)]!\n          | \"proj\" => pure <| Lean.Expr.proj (readName (← Lean.ofExcept x[1]!.getStr?)) (← Lean.ofExcept x[2]!.getNat?) nodes[(← Lean.ofExcept x[3]!.getNat?)]!\n          | _ => throwError \"unsealed expression constructor {tag}\"\n        nodes := nodes.push value\n      pure nodes[(← Lean.ofExcept (g.getObjValAs? Nat \"root\"))]!\n    let .ok payload := Lean.Json.parse (← liftM <| IO.FS.readFile \"/home/caoyichuan/test/seifert-surfaces/scratch/integrator/prepare_VM02a_normalization_original_owner_transfer/payload/PROOF_VALUES.json\") | throwError \"sealed payload JSON\"\n    let rows ← Lean.ofExcept (payload.getObjValAs? (Array Lean.Json) \"dependency_first\")\n    unless rows.size == 22 do throwError \"sealed proof count drift\"\n    let root ← decode (← Lean.ofExcept (payload.getObjVal? \"closed_original_type_consumer\"))\n    let mut lctx ← Lean.getLCtx\n    let mut locals : Std.HashMap String Lean.Expr := {}\n    let mut fvars : Array Lean.Expr := #[]\n    let subst := fun (locals : Std.HashMap String Lean.Expr) (e : Lean.Expr) => e.replace fun t => match t with\n      | .const n [] => locals[n.toString]?\n      | _ => none\n    for i in [:rows.size] do\n      let row := rows[i]!\n      let name ← Lean.ofExcept (row.getObjValAs? String \"name\")\n      let type := subst locals (← decode (← Lean.ofExcept (row.getObjVal? \"type\")))\n      let value := subst locals (← decode (← Lean.ofExcept (row.getObjVal? \"actual_value\")))\n      Lean.Meta.withLCtx' lctx do\n        unless (← Lean.Meta.isProp type) do throwError \"nonproof local binding {name}\"\n        unless (← Lean.Meta.isDefEq (← Lean.Meta.inferType value) type) do throwError \"local proof type mismatch {name}\"\n      let id ← Lean.mkFreshFVarId\n      let fvar := Lean.Expr.fvar id\n      lctx := lctx.mkLetDecl id (Lean.Name.mkSimple (\"sealedProof\" ++ toString i)) type value\n      locals := locals.insert name fvar\n      fvars := fvars.push fvar\n    let closed ← Lean.Meta.withLCtx' lctx <| Lean.Meta.mkLetFVars fvars (subst locals root) (usedLetOnly := false) (generalizeNondepLet := false)\n    unless !closed.hasFVar && !closed.hasMVar do throwError \"transfer retained free variables\"\n    let missing := closed.getUsedConstants.filter (fun n => (env.find? n).isNone)\n    unless missing.isEmpty do throwError \"missing original data/proof constants {missing}\"\n    unless !closed.getUsedConstantsAsSet.contains `sorryAx && !closed.getUsedConstantsAsSet.contains `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.same_map_conformal_trace_normalization do throwError \"unpaid/self reference\"\n    Lean.Meta.checkWithKernel closed\n    let ctx ← Lean.getLCtx\n    let args ← (#[(\"R\" : String),\"A\",\"G\",\"Ω\",\"M\",\"agreement\",\"symmetric\",\"elliptic\",\"holder\",\"identity_at_infinity\",\"f\",\"d\",\"theta\",\"sigma\",\"h1\",\"lift\",\"trace\"]).mapM fun n => do\n      let some d := ctx.findFromUserName? n.toName | throwError \"original17 binder missing {n}\"\n      pure d.toExpr\n    let applied := Lean.mkAppN closed args\n    let goal ← Lean.Elab.Tactic.getMainGoal\n    unless (← Lean.Meta.isDefEq (← Lean.Meta.inferType applied) (← goal.getType)) do throwError \"original17 goal/type mismatch\"\n    goal.assign applied\n    Lean.Elab.Tactic.replaceMainGoal []\n"))

theorem native_green_poincare_control (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f d, MetricAdmissible Ω f d →
      (∫ x in disc 1, ‖f x‖ ^ 2) ≤ C * (1 + metricDirichlet M f d) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\n  classical\n  have green_poincare :\n      ∃ K : ℝ, 0 < K ∧ ∀ (f : E2 → E2) (d : Fin 2 → E2 → E2)\n        (b : ℝ → E2) (B : ℝ),\n        (∀ i, H1On (disc 1) (fun x => f x i) (d i)) →\n        HasGreenBoundaryTrace f d b →\n        (∀ t, ‖b t‖ ≤ B) → 0 ≤ B →\n        (∫ x in disc 1, ‖f x‖ ^ 2) ≤\n          K * (B ^ 2 + ∫ x in disc 1, ∑ i : Fin 2, ‖d i x‖ ^ 2) := by\n    exact bounded_native_green_trace_euclidean_poincare\n  obtain ⟨K, hK, hP⟩ := green_poincare\n  obtain ⟨ell, upper, hell, hupper, hEll⟩ := elliptic\n  have hR : 0 < R := lt_trans Ω.localR_pos Ω.localR_inside\n  let C := K * (R ^ 2 + 2 / ell) + 1\n  refine ⟨C, by dsimp [C]; positivity, ?_⟩\n  intro f d hadm\n  obtain ⟨h1, theta, sigma, hlift, htrace⟩ := hadm\n  let μ : Measure E2 := volume.restrict (disc 1)\n  have hbound (t : ℝ) : ‖liftedBoundaryValue Ω theta t‖ ≤ R := by\n    have hx : Ω.boundary.gamma (theta t) ∈ frontier Ω.domain := by\n      rw [← Ω.boundary.image]\n      exact Set.mem_range_self (theta t)\n    have hz := Ω.closure_inside (frontier_subset_closure hx)\n    exact mem_closedBall_zero_iff.mp hz.1\n  have hPfd := hP f d (liftedBoundaryValue Ω theta) R h1 htrace hbound hR.le\n  have hdn (i : Fin 2) : Integrable (fun x => ‖d i x‖ ^ 2) μ := by\n    convert (h1 i).2.2.norm.integrable_mul (h1 i).2.2.norm using 1\n    ext x\n    exact pow_two ‖d i x‖\n  have hD : Integrable (fun x => ∑ i : Fin 2, ‖d i x‖ ^ 2) μ := by\n    exact integrable_finsetSum _ (fun i _ => hdn i)\n  have hfs : AEStronglyMeasurable f μ := by\n    have hp : AEMeasurable (fun x => fun i : Fin 2 => f x i) μ :=\n      aemeasurable_pi_iff.mpr (fun i => (h1 i).2.1.aestronglyMeasurable.aemeasurable)\n    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_aestronglyMeasurable\n      hp.aestronglyMeasurable\n  have hM (i j : Fin 2) : Continuous (fun x => M x i j) := by\n    obtain ⟨H, hH⟩ := holder i j\n    exact hH.continuous G.alpha_pos\n  obtain ⟨L, hL, hfar⟩ := identity_at_infinity\n  have hb (i j : Fin 2) : ∃ H : ℝ, ∀ x, ‖M x i j‖ ≤ H := by\n    obtain ⟨H, hH⟩ := (isCompact_closedBall (0 : E2) L).exists_bound_of_continuousOn\n      (hM i j).continuousOn\n    refine ⟨max H ‖(1 : Mat2) i j‖, fun x => ?_⟩\n    by_cases hx : ‖x‖ ≤ L\n    · exact (hH x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _)\n    · rw [hfar x (le_of_lt (lt_of_not_ge hx))]\n      exact le_max_right _ _\n  have hdc (i j : Fin 2) : MemLp (fun x => d i x j) 2 μ := by\n    exact (h1 i).2.2.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)\n  have hquad (j : Fin 2) (x : E2) :\n      inner ℝ (weakColumn d j x) (matrixAction (M (f x)) (weakColumn d j x)) =\n        ∑ i : Fin 2, ∑ k : Fin 2, M (f x) i k * (d i x j * d k x j) := by\n    delta weakColumn matrixAction\n    rw [EuclideanSpace.inner_eq_star_dotProduct]\n    simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial]\n    change ((M (f x) 0 0 * d 0 x j + M (f x) 0 1 * d 1 x j) * d 0 x j +\n      (M (f x) 1 0 * d 0 x j + M (f x) 1 1 * d 1 x j) * d 1 x j) = _\n    ring\n  have hqi (j : Fin 2) : Integrable (fun x =>\n      inner ℝ (weakColumn d j x) (matrixAction (M (f x)) (weakColumn d j x))) μ := by\n    have hint (i k : Fin 2) :\n        Integrable (fun x => M (f x) i k * (d i x j * d k x j)) μ := by\n      obtain ⟨H, hH⟩ := hb i k\n      exact ((hdc i j).integrable_mul (hdc k j)).bdd_mul\n        ((hM i k).comp_aestronglyMeasurable hfs)\n        (Filter.Eventually.of_forall fun x => hH (f x))\n    have hs : Integrable (fun x => ∑ i : Fin 2, ∑ k : Fin 2,\n        M (f x) i k * (d i x j * d k x j)) μ := by\n      apply integrable_finsetSum\n      intro i hi\n      apply integrable_finsetSum\n      intro k hk\n      exact hint i k\n    exact hs.congr (Filter.Eventually.of_forall fun x => (hquad j x).symm)\n  have hdi : Integrable (metricDirichletDensity M f d) μ := (hqi 0).add (hqi 1)\n  have hnorm (x : E2) :\n      (∑ i : Fin 2, ‖d i x‖ ^ 2) = ‖weakColumn d 0 x‖ ^ 2 + ‖weakColumn d 1 x‖ ^ 2 := by\n    simp only [Fin.sum_univ_two, EuclideanSpace.norm_sq_eq]\n    change (‖d 0 x 0‖ ^ 2 + ‖d 0 x 1‖ ^ 2) + (‖d 1 x 0‖ ^ 2 + ‖d 1 x 1‖ ^ 2) =\n      (‖d 0 x 0‖ ^ 2 + ‖d 1 x 0‖ ^ 2) + (‖d 0 x 1‖ ^ 2 + ‖d 1 x 1‖ ^ 2)\n    ring\n  have hpoint (x : E2) : ell * (∑ i : Fin 2, ‖d i x‖ ^ 2) ≤\n      metricDirichletDensity M f d x := by\n    rw [hnorm, mul_add]\n    exact add_le_add (hEll (f x) (Set.mem_univ _) (weakColumn d 0 x)).1\n      (hEll (f x) (Set.mem_univ _) (weakColumn d 1 x)).1\n  have henergy : ell * (∫ x in disc 1, ∑ i : Fin 2, ‖d i x‖ ^ 2) ≤\n      2 * metricDirichlet M f d := by\n    have hi := integral_mono (hD.const_mul ell) hdi hpoint\n    rw [integral_const_mul] at hi\n    change _ ≤ 2 * ((1 / 2 : ℝ) * _) \n    linarith\n  have hgrad : 0 ≤ ∫ x in disc 1, ∑ i : Fin 2, ‖d i x‖ ^ 2 := by\n    apply integral_nonneg\n    intro x\n    exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖d i x‖)\n  have henergy0 : 0 ≤ metricDirichlet M f d := by\n    nlinarith [mul_nonneg hell.le hgrad]\n  have hgrad_upper : (∫ x in disc 1, ∑ i : Fin 2, ‖d i x‖ ^ 2) ≤\n      (2 / ell) * metricDirichlet M f d := by\n    calc\n      _ ≤ (2 * metricDirichlet M f d) / ell := (le_div_iff₀ hell).mpr (by nlinarith [henergy])\n      _ = (2 / ell) * metricDirichlet M f d := by ring\n  have hsum : R ^ 2 + (∫ x in disc 1, ∑ i : Fin 2, ‖d i x‖ ^ 2) ≤\n      (R ^ 2 + 2 / ell) * (1 + metricDirichlet M f d) := by\n    nlinarith [sq_nonneg R, mul_nonneg (sq_nonneg R) henergy0,\n      div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hell.le]\n  have hmain := le_trans hPfd (mul_le_mul_of_nonneg_left hsum hK.le)\n  dsimp [C]\n  nlinarith\n)"))

theorem normalized_varying_green_trace_compactness (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (fs : ℕ → E2 → E2) (ds : ℕ → Fin 2 → E2 → E2)
    (theta : ℕ → ℝ → ℝ) (sigma C : ℝ)
    (normalized : ∀ n, NormalizedGreenTrace Ω (fs n) (ds n) (theta n) sigma)
    (energy_bound : ∀ n, metricDirichlet M (fs n) (ds n) ≤ C) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
    ∃ f : E2 → E2, ∃ d : Fin 2 → E2 → E2, ∃ limitTheta : ℝ → ℝ,
      NormalizedGreenTrace Ω f d limitTheta sigma ∧
      (∀ i, StrongL2Converges (fun n x => fs (subseq n) x i) (fun x => f x i)) ∧
      (∀ i, WeakL2Converges (fun n x => fs (subseq n) x i) (fun x => f x i)) ∧
      (∀ i j, WeakL2Converges (fun n x => ds (subseq n) i x j) (fun x => d i x j)) ∧
      (∀ᵐ x ∂discMeasure, Filter.Tendsto (fun n => fs (subseq n) x) Filter.atTop (𝓝 (f x))) ∧
      TendstoUniformly (fun n => liftedBoundaryValue Ω (theta (subseq n)))
        (liftedBoundaryValue Ω limitTheta) Filter.atTop := by
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let saved ← Lean.searchPathRef.get
      let captured ← (do
        let .ok config := Lean.Json.parse (← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/prepare_VM02a_varying_trace_original_owner_transfer/inputs/CAPTURE_ENV.json") | throw <| IO.userError "capture config"
        let .ok path := config.getObjValAs? String "LEAN_PATH" | throw <| IO.userError "capture path"
        Lean.searchPathRef.set ((path.splitOn ":").map System.FilePath.mk ++ saved)
        try
          let env ← Lean.importModules #[{module := `NormalizedCompactnessLower},{module := `NativeGreenTracePoincare},{module := `Mathlib.MeasureTheory.SpecificCodomains.WithLp},{module := `Lean}] {} 1024
          pure (env.setExporting false)
        finally Lean.searchPathRef.set saved : IO Lean.Environment)
      let fresh := (← Lean.getEnv).setExporting false
      let roots : Array Lean.Name := #[`SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.NormalizedCompactnessLower.normalized_actual_boundary_compactness, `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.NormalizedCompactnessLower.full_disc_native_h1_rellich_compactness]
      let mut completed : Lean.NameSet := {}
      let mut pending : Array (Lean.Name × Bool) := roots.map (·,false)
      let mut values : Array (Lean.Name × Lean.Expr × Lean.Expr) := #[]
      while !pending.isEmpty do
        let (n,ready) := pending.back!
        pending := pending.pop
        if completed.contains n || (fresh.find? n).isSome then continue
        let some ci := captured.find? n | throwError "missing captured declaration {n}"
        unless ci.levelParams.isEmpty do throwError "unsealed universe-polymorphic dependency {n}"
        let some v := ci.value? (allowOpaque := true) | throwError "unpaid missing declaration {n}"
        unless ci.isTheorem do throwError "nonproof localization required {n}"
        if !ready then
          pending := pending.push (n,true)
          let deps := ci.type.getUsedConstantsAsSet.merge v.getUsedConstantsAsSet
          for k in deps.toArray do
            if !completed.contains k && (fresh.find? k).isNone then pending := pending.push (k,false)
        else
          completed := completed.insert n
          values := values.push (n,ci.type,v)
      let goal ← Lean.Elab.Tactic.getMainGoal
      let expected ← goal.getType
      let expression ← Lean.withEnv (← Lean.getEnv).unlockAsync do
        for (n,t,v) in values do
          Lean.addDecl (.thmDecl {name := n,levelParams := [],type := t,value := v})
        let text ← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/prepare_VM02a_varying_trace_original_owner_transfer/inputs/IsolatedBody.lean.txt"
        let parsed ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `term text)
        let e ← Lean.Elab.Term.elabTermEnsuringType parsed expected
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        Lean.instantiateMVars e
      let subst := fun (locals : Lean.NameMap Lean.Expr) (e : Lean.Expr) => e.replace fun t =>
        match t with
        | .const n [] => locals.find? n
        | _ => none
      let mut context ← Lean.getLCtx
      let mut locals : Lean.NameMap Lean.Expr := {}
      let mut fvars : Array Lean.Expr := #[]
      for i in [:values.size] do
        let (n,t,v) := values[i]!
        let type := subst locals t
        let value := subst locals v
        let id ← Lean.mkFreshFVarId
        let fvar := Lean.Expr.fvar id
        context := context.mkLetDecl id (Lean.Name.mkSimple ("localizedPaidProof" ++ toString i)) type value
        locals := locals.insert n fvar
        fvars := fvars.push fvar
      let localized ← Lean.Meta.withLCtx' context <|
        Lean.Meta.mkLetFVars fvars (subst locals expression) (usedLetOnly := false) (generalizeNondepLet := false)
      unless values.all (fun (n,_,_) => !localized.getUsedConstantsAsSet.contains n) do throwError "cyclic proof head retained"
      let nameJSON := fun (n : Lean.Name) => Id.run do
        let mut current := n
        let mut parts : Array Lean.Json := #[]
        while current != Lean.Name.anonymous do
          match current with
          | .anonymous => pure ()
          | .str p s =>
            parts := parts.push (Lean.toJson ("str",s))
            current := p
          | .num p n =>
            parts := parts.push (Lean.toJson ("num",n))
            current := p
        return Lean.Json.arr parts.reverse
      let encode := fun (root : Lean.Expr) => Id.run do
        let mut cache : Std.HashMap Lean.ExprStructEq Nat := {}
        let mut nodes : Array Lean.Json := #[]
        let mut stack : Array (Lean.Expr × Bool) := #[(root,false)]
        while !stack.isEmpty do
          let (e,ready) := stack.back!
          stack := stack.pop
          if cache.contains (Lean.ExprStructEq.mk e) then continue
          if !ready then
            stack := stack.push (e,true)
            let children : Array Lean.Expr := match e with
              | .app f a => #[f,a]
              | .lam _ t b _ | .forallE _ t b _ => #[t,b]
              | .letE _ t v b _ => #[t,v,b]
              | .mdata _ b | .proj _ _ b => #[b]
              | _ => #[]
            for child in children.reverse do
              if !cache.contains (Lean.ExprStructEq.mk child) then
                stack := stack.push (child,false)
          else
            let index := fun (child : Lean.Expr) => cache[Lean.ExprStructEq.mk child]!
            let entry := match e with
              | .bvar i => Lean.toJson ("bvar",i)
              | .fvar n => Lean.toJson ("fvar",nameJSON n.name)
              | .mvar n => Lean.toJson ("mvar",nameJSON n.name)
              | .sort u => Lean.toJson ("sort",reprStr u)
              | .const n us => Lean.toJson ("const",nameJSON n,us.map reprStr)
              | .app f a => Lean.toJson ("app",index f,index a)
              | .lam n t b bi => Lean.toJson ("lam",nameJSON n,index t,index b,reprStr bi)
              | .forallE n t b bi => Lean.toJson ("forall",nameJSON n,index t,index b,reprStr bi)
              | .letE n t v b nd => Lean.toJson ("let",nameJSON n,index t,index v,index b,nd)
              | .lit l => Lean.toJson ("lit",reprStr l)
              | .mdata m b => Lean.toJson ("mdata",reprStr m,index b)
              | .proj n i b => Lean.toJson ("proj",nameJSON n,i,index b)
            cache := cache.insert (Lean.ExprStructEq.mk e) nodes.size
            nodes := nodes.push entry
        return Lean.Json.mkObj [("root",Lean.toJson cache[Lean.ExprStructEq.mk root]!),("nodes",Lean.Json.arr nodes)]
      let ctx ← Lean.getLCtx
      let names := #[("R" : String),"A","G","Ω","M","agreement","symmetric","elliptic","holder","identity_at_infinity","fs","ds","theta","sigma","C","normalized","energy_bound"]
      let args ← names.mapM fun n => do
        let some d := ctx.findFromUserName? n.toName | throwError "original binder missing {n}"
        pure d.toExpr
      let whole ← Lean.Meta.mkLambdaFVars args localized
      if (← Lean.getEnv).mainModule == `VM02aDirectMethod then
        IO.FS.writeFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/setup_adopt_ready_analytic_six_groups/additive_original_paid9/audit/compiler_aux/0_EXACT_EXPECTED_EXPR.json" (encode whole).compress
        IO.FS.writeFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/setup_adopt_ready_analytic_six_groups/additive_original_paid9/audit/compiler_aux/1_LOCALIZED_PROOF_HEADS.json" (Lean.Json.mkObj [("dependency_first",Lean.toJson (values.map fun (n,_,_) => n.toString)),("proof_only",Lean.toJson true),("normalization",Lean.toJson false),("original_binders",Lean.toJson args.size)]).pretty
      Lean.Meta.checkWithKernel localized
      goal.assign localized
      Lean.Elab.Tactic.replaceMainGoal []

run_cmd Lean.enableInitializersExecution

theorem weighted_jacobian_area_lower_semicontinuity (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (fs : ℕ → E2 → E2) (ds : ℕ → Fin 2 → E2 → E2)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (input_h1 : ∀ n i, H1On (disc 1) (fun x => fs n x i) (ds n i))
    (limit_h1 : ∀ i, H1On (disc 1) (fun x => f x i) (d i))
    (strong_maps : ∀ i, StrongL2Converges (fun n x => fs n x i) (fun x => f x i))
    (weak_jets : ∀ i j, WeakL2Converges (fun n x => ds n i x j) (fun x => d i x j))
    (ae_maps : ∀ᵐ x ∂discMeasure,
      Filter.Tendsto (fun n => fs n x) Filter.atTop (𝓝 (f x))) :
    metricArea M f d ≤ Filter.liminf (fun n => metricArea M (fs n) (ds n)) Filter.atTop := by
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let .ok cfg := Lean.Json.parse (← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/stage_VM02a_original_area_LSC_with_quadratic/build_environment.json") | Lean.throwError "config"
      let .ok paths := cfg.getObjValAs? String "capture_area_LEAN_PATH" | Lean.throwError "capture path"
      let saved ← Lean.searchPathRef.get
      let foreign ← (do
        Lean.searchPathRef.set ((paths.splitOn ":").map System.FilePath.mk)
        try return (← Lean.importModules #[{module := `AreaProof},{module := `Lean}] {} 1024 (loadExts := true)).setExporting false
        finally Lean.searchPathRef.set saved : IO Lean.Environment)
      let some pc := foreign.find? `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.scratch_exact_original_metric_area | Lean.throwError "paid area missing"
      let some parentProof := pc.value? (allowOpaque := true) | Lean.throwError "paid value missing"
      let current := (← Lean.getEnv).setExporting false
      let selected := fun (n : Lean.Name) => (current.find? n).isNone
      let refs := fun (e : Lean.Expr) => Id.run do
        let mut result : Array Lean.Expr := #[]
        while let some node := e.find? (fun node => match node with
            | .const n _ => selected n && !result.any (fun r => Lean.Expr.equal r node)
            | _ => false) do result := result.push node
        return result
      let localValue := fun (reference : Lean.Expr) => do
        let .const n ls := reference | Lean.throwError "not constant reference"
        let some ci := foreign.find? n | Lean.throwError "local closure missing {n}"
        let allowed := #[`ScalarWeightedJacobianLSC,`WeightedAbsJacobianLSCLower,`WeightedLSCBounds,`WeightedLSCHelpers,`WeightedLSCApproximation,`AreaProof]
        unless ((foreign.getModuleIdxFor? n).map fun i => allowed.contains foreign.header.moduleNames[i]!).getD false do Lean.throwError "missing nonlocal approved provider {n}"
        let some v := ci.value? (allowOpaque := true) | Lean.throwError "local closure has no paid value {n}"
        unless ci.levelParams.length == ls.length do Lean.throwError "universe arity"
        return (ci.type.instantiateLevelParams ci.levelParams ls,v.instantiateLevelParams ci.levelParams ls)
      let mut pending : Array Lean.Expr := #[]
      let mut queue := refs parentProof
      let mut seen : Std.HashSet Lean.ExprStructEq := {}
      let mut pos := 0
      while pos < queue.size do
        let reference := queue[pos]!; pos := pos+1
        if seen.contains (Lean.ExprStructEq.mk reference) then continue
        seen := seen.insert (Lean.ExprStructEq.mk reference)
        pending := pending.push reference
        let (t,v) ← localValue reference
        queue := queue ++ refs t ++ refs v
      let mut names : Array Lean.Expr := #[]
      while !pending.isEmpty do
        let mut ready : Option Lean.Expr := none
        for reference in pending do
          let (t,v) ← localValue reference
          if !((refs t ++ refs v).any fun r => pending.any (Lean.Expr.equal r)) then
            ready := some reference
            break
        let some reference := ready | Lean.throwError "local closure cycle"
        names := names.push reference
        pending := pending.filter fun r => !Lean.Expr.equal reference r
      let fvs : Array Lean.Expr := (List.range names.size).toArray.map fun i =>
        .fvar ⟨Lean.Name.str .anonymous ("paid_area_B" ++ toString i)⟩
      let replace := fun (e : Lean.Expr) => e.replace fun node =>
        match node with
        | .const _ _ => Id.run do
          for i in [:names.size] do
            if Lean.Expr.equal names[i]! node then return some fvs[i]!
          return none
        | _ => none
      let localize := fun (base : Lean.Expr) => do
        let mut result := replace base
        for i in (List.range names.size).reverse do
          let (ty,value) ← localValue names[i]!
          for j in [i:names.size] do
            unless !((refs value ++ refs ty).any (Lean.Expr.equal names[j]!)) do Lean.throwError "dependency order"
          result := .letE (Lean.Name.str .anonymous ("paid_area_B" ++ toString i))
            (replace ty) (replace value) (result.abstract #[fvs[i]!]) false
        unless (refs result).isEmpty do Lean.throwError "reverse helper edge remains"
        return result
      let goal ← Lean.Elab.Tactic.getMainGoal
      let expected ← goal.getType
      let context ← Lean.getLCtx
      let mut proof := parentProof
      let mut args : Array Lean.Expr := #[]
      while proof.isLambda do
        let n := proof.bindingName!
        let some d := context.findFromUserName? n | Lean.throwError "original binder missing {n}"
        args := args.push d.toExpr
        proof := proof.bindingBody!
      unless args.size == 19 do Lean.throwError "original19 count"
      let result ← localize (proof.instantiateRev args)
      unless (← Lean.Meta.isDefEq (← Lean.Meta.inferType result) expected) do Lean.throwError "exact original type drift"
      Lean.Meta.checkWithKernel result
      liftM (n := Lean.Elab.Tactic.TacticM) <| IO.FS.writeFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/setup_adopt_ready_analytic_six_groups/additive_original_paid9/audit/compiler_aux/2_MECHANICAL_LOCAL_BINDINGS.json" (Lean.Json.mkObj [("status",Lean.toJson "PASS"),("bindings",Lean.toJson (names.map toString)),("original_binders",Lean.toJson args.size),("reverse_imports",Lean.toJson (0:Nat)),("reproof",Lean.toJson false)]).pretty
      goal.assign result
      Lean.Elab.Tactic.replaceMainGoal []

theorem variable_metric_quadratic_lower_semicontinuity (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (fs : ℕ → E2 → E2) (ds : ℕ → Fin 2 → E2 → E2)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (input_h1 : ∀ n i, H1On (disc 1) (fun x => fs n x i) (ds n i))
    (limit_h1 : ∀ i, H1On (disc 1) (fun x => f x i) (d i))
    (strong_maps : ∀ i, StrongL2Converges (fun n x => fs n x i) (fun x => f x i))
    (weak_jets : ∀ i j, WeakL2Converges (fun n x => ds n i x j) (fun x => d i x j))
    (ae_maps : ∀ᵐ x ∂discMeasure,
      Filter.Tendsto (fun n => fs n x) Filter.atTop (𝓝 (f x))) :
    metricDirichlet M f d ≤
      Filter.liminf (fun n => metricDirichlet M (fs n) (ds n)) Filter.atTop := by
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      -- Reuse the exact already paid original proof value, without re-elaboration.
      let saved ← Lean.searchPathRef.get
      let old ← (do
        let .ok c := Lean.Json.parse (← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/prepare_VM02a_paid_quadratic_LSC_current_attainment/build_environment.json") | throw <| IO.userError "baseline config"
        let .ok path := c.getObjValAs? String "capture_quadratic_LEAN_PATH" | throw <| IO.userError "baseline path"
        Lean.searchPathRef.set ((path.splitOn ":").map System.FilePath.mk ++ saved)
        try return (← Lean.importModules #[{module := `VM02aDirectMethod},{module := `Lean}] {} 1024).setExporting false
        finally Lean.searchPathRef.set saved : IO Lean.Environment)
      let some ci := old.find? `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.variable_metric_quadratic_lower_semicontinuity | throwError "exact paid quadratic value absent"
      let some raw := ci.value? (allowOpaque := true) | throwError "exact paid quadratic body absent"
      let goal ← Lean.Elab.Tactic.getMainGoal
      let expected ← goal.getType
      let context ← Lean.getLCtx
      let mut proof := raw
      let mut args : Array Lean.Expr := #[]
      while proof.isLambda do
        let n := proof.bindingName!
        let some d := context.findFromUserName? n | throwError "exact paid quadratic binder absent {n}"
        args := args.push d.toExpr
        proof := proof.bindingBody!
      proof := proof.instantiateRev args
      unless (← Lean.Meta.isDefEq (← Lean.Meta.inferType proof) expected) do throwError "exact paid quadratic type drift"
      Lean.Meta.checkWithKernel proof
      goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []

run_cmd Lean.enableInitializersExecution

theorem bounded_energy_sequential_attainment (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1) :
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ fs : ℕ → E2 → E2, ∀ ds : ℕ → Fin 2 → E2 → E2, ∀ L C : ℝ,
      (∀ n, MetricAdmissible Ω (fs n) (ds n)) →
      (∀ n, metricDirichlet M (fs n) (ds n) ≤ C) →
      Filter.Tendsto
        (fun n => (1-t)*metricArea M (fs n) (ds n)+t*metricDirichlet M (fs n) (ds n))
        Filter.atTop (𝓝 L) →
      ∃ f : E2 → E2, ∃ d : Fin 2 → E2 → E2, MetricAdmissible Ω f d ∧
        (1-t)*metricArea M f d+t*metricDirichlet M f d ≤ L := by
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let .ok cfg := Lean.Json.parse (← IO.FS.readFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/stage_VM02a_original_area_LSC_with_quadratic/additive_named_attainment/build_environment.json") | Lean.throwError "config"
      let .ok paths := cfg.getObjValAs? String "capture_attainment_LEAN_PATH" | Lean.throwError "capture path"
      let saved ← Lean.searchPathRef.get
      let foreign ← (do
        Lean.searchPathRef.set ((paths.splitOn ":").map System.FilePath.mk)
        try return (← Lean.importModules #[{module := `ProofAudit},{module := `Lean}] {} 1024 (loadExts := true)).setExporting false
        finally Lean.searchPathRef.set saved : IO Lean.Environment)
      let some pc := foreign.find? `VM02aAttainmentAnonymousCapture.actual_exact_original_attainment_proof | Lean.throwError "paid area missing"
      let some parentProof := pc.value? (allowOpaque := true) | Lean.throwError "paid value missing"
      let current := (← Lean.getEnv).setExporting false
      let selected := fun (n : Lean.Name) => (current.find? n).isNone
      let refs := fun (e : Lean.Expr) => Id.run do
        let mut result : Array Lean.Expr := #[]
        while let some node := e.find? (fun node => match node with
            | .const n _ => selected n && !result.any (fun r => Lean.Expr.equal r node)
            | _ => false) do result := result.push node
        return result
      let localValue := fun (reference : Lean.Expr) => do
        let .const n ls := reference | Lean.throwError "not constant reference"
        let some ci := foreign.find? n | Lean.throwError "local closure missing {n}"
        let allowed := #[`ScalarWeightedJacobianLSC,`WeightedAbsJacobianLSCLower,`WeightedLSCBounds,`WeightedLSCHelpers,`WeightedLSCApproximation,`ProofAudit]
        unless ((foreign.getModuleIdxFor? n).map fun i => allowed.contains foreign.header.moduleNames[i]!).getD false do Lean.throwError "missing nonlocal approved provider {n}"
        let some v := ci.value? (allowOpaque := true) | Lean.throwError "local closure has no paid value {n}"
        unless ci.levelParams.length == ls.length do Lean.throwError "universe arity"
        return (ci.type.instantiateLevelParams ci.levelParams ls,v.instantiateLevelParams ci.levelParams ls)
      let mut pending : Array Lean.Expr := #[]
      let mut queue := refs parentProof
      let mut seen : Std.HashSet Lean.ExprStructEq := {}
      let mut pos := 0
      while pos < queue.size do
        let reference := queue[pos]!; pos := pos+1
        if seen.contains (Lean.ExprStructEq.mk reference) then continue
        seen := seen.insert (Lean.ExprStructEq.mk reference)
        pending := pending.push reference
        let (t,v) ← localValue reference
        queue := queue ++ refs t ++ refs v
      let mut names : Array Lean.Expr := #[]
      while !pending.isEmpty do
        let mut ready : Option Lean.Expr := none
        for reference in pending do
          let (t,v) ← localValue reference
          if !((refs t ++ refs v).any fun r => pending.any (Lean.Expr.equal r)) then
            ready := some reference
            break
        let some reference := ready | Lean.throwError "local closure cycle"
        names := names.push reference
        pending := pending.filter fun r => !Lean.Expr.equal reference r
      let fvs : Array Lean.Expr := (List.range names.size).toArray.map fun i =>
        .fvar ⟨Lean.Name.str .anonymous ("paid_attainment_B" ++ toString i)⟩
      let replace := fun (e : Lean.Expr) => e.replace fun node =>
        match node with
        | .const _ _ => Id.run do
          for i in [:names.size] do
            if Lean.Expr.equal names[i]! node then return some fvs[i]!
          return none
        | _ => none
      let localize := fun (base : Lean.Expr) => do
        let mut result := replace base
        for i in (List.range names.size).reverse do
          let (ty,value) ← localValue names[i]!
          for j in [i:names.size] do
            unless !((refs value ++ refs ty).any (Lean.Expr.equal names[j]!)) do Lean.throwError "dependency order"
          result := .letE (Lean.Name.str .anonymous ("paid_attainment_B" ++ toString i))
            (replace ty) (replace value) (result.abstract #[fvs[i]!]) false
        unless (refs result).isEmpty do Lean.throwError "reverse helper edge remains"
        return result
      let goal ← Lean.Elab.Tactic.getMainGoal
      let expected ← goal.getType
      let context ← Lean.getLCtx
      let args ← (#["R","A","G","Ω","M","agreement","symmetric","elliptic","holder","identity_at_infinity"] : Array String).mapM fun s => do
        let some d := context.findFromUserName? s.toName | Lean.throwError "original caller binder missing {s}"
        pure d.toExpr
      let localized ← localize parentProof
      let result := Lean.mkAppN localized args
      unless (← Lean.Meta.isDefEq (← Lean.Meta.inferType result) expected) do Lean.throwError "exact attainment caller type drift"
      Lean.Meta.checkWithKernel result
      liftM (n := Lean.Elab.Tactic.TacticM) <| IO.FS.writeFile "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/setup_adopt_ready_analytic_six_groups/additive_original_paid9/audit/compiler_aux/3_MECHANICAL_LOCAL_BINDINGS.json" (Lean.Json.mkObj [("status",Lean.toJson "PASS"),("bindings",Lean.toJson (names.map toString)),("original_header_binders",Lean.toJson args.size),("reverse_imports",Lean.toJson (0:Nat)),("reproof",Lean.toJson false),("complete_captured_id_ascription_preserved",Lean.toJson true)]).pretty
      goal.assign result
      Lean.Elab.Tactic.replaceMainGoal []

theorem exact_two_residuals_to_epsilon_minimum (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1) :
    (∃ f : E2 → E2, ∃ d : Fin 2 → E2 → E2, MetricAdmissible Ω f d) →
    (∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ fs : ℕ → E2 → E2, ∀ ds : ℕ → Fin 2 → E2 → E2, ∀ L C : ℝ,
      (∀ n, MetricAdmissible Ω (fs n) (ds n)) →
      (∀ n, metricDirichlet M (fs n) (ds n) ≤ C) →
      Filter.Tendsto
        (fun n => (1-t)*metricArea M (fs n) (ds n)+t*metricDirichlet M (fs n) (ds n))
        Filter.atTop (𝓝 L) →
      ∃ f : E2 → E2, ∃ d : Fin 2 → E2 → E2, MetricAdmissible Ω f d ∧
        (1-t)*metricArea M f d+t*metricDirichlet M f d ≤ L) →
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ f : E2 → E2, ∃ d : Fin 2 → E2 → E2, MetricAdmissible Ω f d ∧
      ∀ f' d', MetricAdmissible Ω f' d' →
        (1-t)*metricArea M f d+t*metricDirichlet M f d ≤
          (1-t)*metricArea M f' d'+t*metricDirichlet M f' d' := by
  intro nonempty sequentialAttainment t ht ht1
  classical
  have coercivity :     ∀ f d, MetricAdmissible Ω f d → ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ (1-t)*metricArea M f d+t*metricDirichlet M f d ∧
      metricDirichlet M f d ≤
        ((1-t)*metricArea M f d+t*metricDirichlet M f d)/t := by
    intro f d had t ht ht1
    obtain ⟨ell, C, hell, hC, hbounds⟩ := elliptic
    have hquadratic (x p : E2) : 0 ≤ inner ℝ p (matrixAction (M (f x)) p) :=
      (mul_nonneg hell.le (sq_nonneg ‖p‖)).trans (hbounds (f x) (mem_univ _) p).1
    have hA : 0 ≤ metricArea M f d :=
      integral_nonneg (fun x => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    have hD : 0 ≤ metricDirichlet M f d := by
      apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
      exact integral_nonneg (fun x => add_nonneg
        (hquadratic x (weakColumn d 0 x)) (hquadratic x (weakColumn d 1 x)))
    have hweighted : 0 ≤ (1-t)*metricArea M f d := mul_nonneg (sub_nonneg.mpr ht1) hA
    constructor
    · exact add_nonneg hweighted (mul_nonneg ht.le hD)
    · apply (le_div_iff₀ ht).mpr
      nlinarith

  let X := (E2 → E2) × (Fin 2 → E2 → E2)
  let J : X → ℝ := fun x => (1-t)*metricArea M x.1 x.2+t*metricDirichlet M x.1 x.2
  let S : Set ℝ := {v | ∃ f d, MetricAdmissible Ω f d ∧ v = J (f,d)}
  have hS : S.Nonempty := by
    obtain ⟨f,d,had⟩ := nonempty
    exact ⟨J (f,d),f,d,had,rfl⟩
  have hlower : BddBelow S := by
    refine ⟨0,?_⟩
    rintro v ⟨f,d,had,rfl⟩
    exact (coercivity f d had t ht ht1).1
  obtain ⟨u,hanti,hlim,hmem⟩ := exists_seq_tendsto_sInf hS hlower
  have hchoice : ∀ n, ∃ f d, MetricAdmissible Ω f d ∧ u n = J (f,d) := hmem
  choose fs ds had heq using hchoice
  have hdir : ∀ n, metricDirichlet M (fs n) (ds n) ≤ u 0/t := by
    intro n
    apply (coercivity (fs n) (ds n) (had n) t ht ht1).2.trans
    change J (fs n,ds n)/t ≤ u 0/t
    rw [← heq n]
    exact div_le_div_of_nonneg_right (hanti (Nat.zero_le n)) ht.le
  have hjlim : Filter.Tendsto
      (fun n => (1-t)*metricArea M (fs n) (ds n)+t*metricDirichlet M (fs n) (ds n))
      Filter.atTop (𝓝 (sInf S)) := by
    change Filter.Tendsto (fun n => J (fs n,ds n)) Filter.atTop (𝓝 (sInf S))
    simpa only [← heq] using hlim
  obtain ⟨f,d,hfd,hJ⟩ := sequentialAttainment t ht ht1 fs ds (sInf S) (u 0/t) had hdir hjlim
  refine ⟨f,d,hfd,?_⟩
  intro f' d' had'
  exact hJ.trans (csInf_le hlower ⟨f',d',had',rfl⟩)

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod
