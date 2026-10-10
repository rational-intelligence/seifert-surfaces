import B1L1IndependentLower

noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
open SeifertSurfaces.AppendixACoordinates

private theorem paid_boundary_cap_paste_v460 {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (f h : E2 → E2) (d dh : Fin 2 → E2 → E2)
    (base_H1 : ∀ i, H1On (disc 1) (fun z => f z i) (d i))
    (theta theta' : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (new_lift : WeakMonotoneBoundaryLift Ω theta' sigma)
    (x : E2) (center : x ∈ closedDisc 1) (r : ℝ) (radius : 0 < r)
    (local_H1 : ∀ i, H1On (planarCap x r) (fun z => h z i) (dh i))
    (unchanged_trace : ∀ t ∈ Icc 0 (2 * Real.pi),
      unitCircleParameter t ∉ Metric.ball x r →
      liftedBoundaryValue Ω theta' t = liftedBoundaryValue Ω theta t)
    (seam : RelativeCapGreen x r f h d dh
      (liftedBoundaryValue Ω theta) (liftedBoundaryValue Ω theta')) :
    (∀ i, H1On (disc 1) (fun z => pastedMap (planarCap x r) f h z i)
      (pastedJets (planarCap x r) d dh i)) ∧
    HasGreenBoundaryTrace (pastedMap (planarCap x r) f h)
      (pastedJets (planarCap x r) d dh) (liftedBoundaryValue Ω theta') ∧
    MetricAdmissible Ω (pastedMap (planarCap x r) f h)
      (pastedJets (planarCap x r) d dh)  := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "initial_paid_comparison.olean")
    let ci ← (data.constants.find? (fun c => c.name == `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.boundary_cap_paste)).elim (throwError "sealed comparison declaration missing") pure
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let raw ← (ci.value? (allowOpaque := true)).elim (throwError "sealed comparison proof missing") pure
    if !(ci.levelParams.isEmpty && !raw.hasMVar && !raw.hasFVar) then throwError "sealed comparison closed proof drift"
    Lean.Meta.checkWithKernel raw
    let args ← ([`R, `Ω, `f, `h, `d, `dh, `base_H1, `theta, `theta', `sigma, `lift, `trace, `new_lift, `x, `center, `r, `radius, `local_H1, `unchanged_trace, `seam].toArray.mapM
      fun n=>Lean.Elab.Term.elabTerm (Lean.mkIdent n) none)
    let term := Lean.mkAppN raw args
    let inferred ← Lean.Meta.inferType term
    if !(inferred == target) then
      unless ← Lean.Meta.isDefEq inferred target do throwError "exact sealed comparison type mismatch"
    Lean.Meta.checkWithKernel term
    goal.assign term
    Lean.Elab.Tactic.replaceMainGoal []

private theorem paid_same_minimizer_local_energy_v460 (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (U : Set E2) (measurable_U : MeasurableSet U) (inside : U ⊆ disc 1)
    (h : E2 → E2) (dh : Fin 2 → E2 → E2)
    (competitor : MetricAdmissible Ω (pastedMap U f h) (pastedJets U d dh))
    (ell Lambda : ℝ) (ell_pos : 0 < ell) (Lambda_pos : 0 < Lambda)
    (bounds : ∀ y : E2, ∀ p : E2,
      ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (M y) p) ∧
      inner ℝ p (matrixAction (M y) p) ≤ Lambda * ‖p‖ ^ 2) :
    IntegrableOn (metricDirichletDensity M f d) U ∧
    IntegrableOn (metricDirichletDensity M h dh) U ∧
    IntegrableOn (euclideanJetDensity d) U ∧
    IntegrableOn (euclideanJetDensity dh) U ∧
    (∀ z ∈ disc 1 \ U,
      metricDirichletDensity M (pastedMap U f h) (pastedJets U d dh) z =
        metricDirichletDensity M f d z) ∧
    (∫ z in U, metricDirichletDensity M f d z) ≤
      ∫ z in U, metricDirichletDensity M h dh z ∧
    (∫ z in U, euclideanJetDensity d z) ≤
      (Lambda / ell) * ∫ z in U, euclideanJetDensity dh z  := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "initial_paid_comparison.olean")
    let ci ← (data.constants.find? (fun c => c.name == `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.same_minimizer_local_energy)).elim (throwError "sealed comparison declaration missing") pure
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let raw ← (ci.value? (allowOpaque := true)).elim (throwError "sealed comparison proof missing") pure
    if !(ci.levelParams.isEmpty && !raw.hasMVar && !raw.hasFVar) then throwError "sealed comparison closed proof drift"
    Lean.Meta.checkWithKernel raw
    let args ← ([`R, `A, `G, `Ω, `M, `agreement, `symmetric, `elliptic, `holder, `identity_at_infinity, `f, `d, `minimum, `U, `measurable_U, `inside, `h, `dh, `competitor, `ell, `Lambda, `ell_pos, `Lambda_pos, `bounds].toArray.mapM
      fun n=>Lean.Elab.Term.elabTerm (Lean.mkIdent n) none)
    let term := Lean.mkAppN raw args
    let inferred ← Lean.Meta.inferType term
    if !(inferred == target) then
      unless ← Lean.Meta.isDefEq inferred target do throwError "exact sealed comparison type mismatch"
    Lean.Meta.checkWithKernel term
    goal.assign term
    Lean.Elab.Tactic.replaceMainGoal []

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
