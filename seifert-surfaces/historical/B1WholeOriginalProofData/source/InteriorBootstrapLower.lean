import InteriorPotentialData
noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential
open SeifertSurfaces.AppendixACoordinates

/-- R1: one finite exponent sufficient for the original-alpha route. -/
theorem finite_q_interior_bootstrap
    (alpha : ℝ≥0) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (lam Lambda : ℝ) (hlam : 0 < lam) (hLambda : 0 < Lambda) (HN : ℝ≥0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ d : InteriorData alpha lam Lambda HN,
        MemLp d.dv (ENNReal.ofReal (bootstrapExponent alpha))
          (volume.restrict (Metric.ball (0 : E2) (7 / 8))) ∧
        eLpNorm d.dv (ENNReal.ofReal (bootstrapExponent alpha))
          (volume.restrict (Metric.ball (0 : E2) (7 / 8))) ≤
            ENNReal.ofReal (C * dataSize d) ∧
        ∃ (wH : E2 → ℝ) (Hw : ℝ≥0),
          wH =ᵐ[volume.restrict (Metric.ball (0 : E2) (7 / 8))] normalizedScalar d ∧
          HolderOnWith Hw (scalarExponent alpha) wH (Metric.ball (0 : E2) (7 / 8)) ∧
          (∀ z ∈ Metric.ball (0 : E2) (7 / 8), |wH z| + (Hw : ℝ) ≤ C * dataSize d) := by
  set_option maxHeartbeats 0 in
    run_tac do
      let current ← Lean.getEnv
      let imported ← Lean.Core.liftIOCore <| Lean.importModules (loadExts := false) #[{module := `R1}] {} (trustLevel := 0)
      let n := `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.finite_q_interior_bootstrap
      let some ci := imported.find? n | throwError "owned complete R1 proof missing"
      let some raw := ci.value? (allowOpaque := true) | throwError "owned complete R1 proof unavailable"
      unless ci.levelParams.isEmpty do throwError "unexpected target universes"
      let mut proof := raw
      let mut rounds := 0
      let mut changed := true
      while changed do
        rounds := rounds + 1
        if rounds > 1000 then throwError "paid proof expansion did not terminate"
        let mut replacements : Std.HashMap Lean.Name (List Lean.Name × Lean.Expr) := {}
        for m in proof.getUsedConstantsAsSet.toArray do
          if (current.find? m).isSome then continue
          let some dep := imported.find? m | throwError "missing dependency {m}"
          let some value := dep.value? (allowOpaque := true) | throwError "foreign primitive {m}"
          replacements := replacements.insert m (dep.levelParams, value)
        changed := !replacements.isEmpty
        if changed then
          proof := proof.replace fun e => match e with
            | .const m us =>
              if let some (params,value) := replacements[m]? then
                some (value.instantiateLevelParams params us)
              else none
            | _ => none
      for m in proof.getUsedConstantsAsSet.toArray do
        unless (current.find? m).isSome do throwError "foreign constant escaped {m}"
        if m == `sorryAx || m == n then throwError "unpaid or circular target dependency {m}"
      unless !proof.hasMVar && !proof.hasFVar do throwError "owned proof not closed"
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let expected ← goal.getType
        let args ← ([`alpha, `halpha, `halpha1, `lam, `Lambda, `hlam, `hLambda, `HN].toArray.mapM fun nm => Lean.Elab.Term.elabTerm (Lean.mkIdent nm) none)
        let proof := Lean.mkAppN proof args
        Lean.Meta.check proof
        let type ← Lean.Meta.inferType proof
        unless ← Lean.Meta.isDefEq type expected do throwError "original native R1 type drift"
        goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []


/-- R2 cutoff atom: uniformly chosen radius and both native forcing terms. -/
theorem uniform_compact_cutoff_data
    (alpha : ℝ≥0) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (lam Lambda : ℝ) (hlam : 0 < lam) (hLambda : 0 < Lambda) (HN : ℝ≥0) :
    ∃ R C : ℝ, 0 < R ∧ R < 1 / 32 ∧ 0 < C ∧
      ∀ (x : E2), x ∈ Metric.closedBall (0 : E2) (3 / 4) →
      ∀ d : InteriorData alpha lam Lambda HN,
        Metric.ball x (2 * R) ⊆ Metric.ball (0 : E2) (7 / 8) ∧
        ∃ chi eta : E2 → ℝ,
          ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧ tsupport chi ⊆ Metric.ball x R ∧
          (∀ z, 0 ≤ chi z ∧ chi z ≤ 1) ∧
          (∀ z ∈ Metric.ball x (R / 2), chi z = 1) ∧
          (∀ z, ‖fderiv ℝ chi z‖ ≤ C / R ∧ ‖iteratedFDeriv ℝ 2 chi z‖ ≤ C / R ^ 2) ∧
          ContDiff ℝ ∞ eta ∧ HasCompactSupport eta ∧ tsupport eta ⊆ Metric.ball x (2 * R) ∧
          (∀ z, 0 ≤ eta z ∧ eta z ≤ 1) ∧
          (∀ z ∈ Metric.ball x R, eta z = 1) ∧
          (let w := normalizedScalar d
           let U := localizedScalar chi w
           let dU := localizedGradient chi w d.dv
           let Echi := localizedVectorData d.N d.F chi w
           let fchi := localizedScalarData d.N d.F d.dv chi
           let Ntilde := extendedCoefficient d.N x eta
           DirectWeak.WeakDivergenceWithData Set.univ Ntilde Echi fchi U dU ∧
           HasCompactSupport U ∧ tsupport U ⊆ Metric.ball x R ∧
           HasCompactSupport dU ∧ tsupport dU ⊆ Metric.ball x R ∧
           HasCompactSupport Echi ∧ tsupport Echi ⊆ Metric.ball x R ∧
           HasCompactSupport fchi ∧ tsupport fchi ⊆ Metric.ball x R ∧
           MemLp Echi 2 volume ∧ MemLp fchi (ENNReal.ofReal (bootstrapExponent alpha)) volume ∧
           Integrable fchi ∧ (∫ z, fchi z) = 0 ∧
           eLpNorm fchi (ENNReal.ofReal (bootstrapExponent alpha)) volume ≤
             ENNReal.ofReal (C * dataSize d) ∧
           (∀ z ∈ tsupport chi, Ntilde z = d.N z) ∧
           (∀ z ∉ Metric.ball x (2 * R), Ntilde z = d.N x) ∧
           SymmetricOn Ntilde Set.univ ∧
           (∀ z, ∀ t : E2,
             lam * ‖t‖ ^ 2 ≤ inner ℝ t (matrixAction (Ntilde z) t) ∧
             ‖matrixAction (Ntilde z) t‖ ≤ Lambda * ‖t‖) ∧
           (∀ i j, HolderWith (Real.toNNReal C * HN) alpha (fun z => Ntilde z i j) ∧
             ∀ z, |Ntilde z i j - d.N x i j| ≤
               C * (HN : ℝ) * Real.rpow R (alpha : ℝ)) ∧
           ∃ (wH : E2 → ℝ) (Hw HE : ℝ≥0) (Ebound : ℝ),
             wH =ᵐ[volume.restrict (Metric.ball (0 : E2) (7 / 8))] w ∧
             HolderOnWith Hw (scalarExponent alpha) wH (Metric.ball (0 : E2) (7 / 8)) ∧
             (let EH := localizedVectorData d.N d.F chi wH
              EH =ᵐ[volume] Echi ∧ HolderWith HE alpha EH ∧
              (∀ z, ‖EH z‖ ≤ Ebound) ∧ 0 ≤ Ebound ∧
              Ebound + (HE : ℝ) ≤ C * dataSize d)) := by set_option maxHeartbeats 0 in run_tac do { let current ← Lean.getEnv; let imported ← Lean.Core.liftIOCore <| Lean.importModules (loadExts := false) #[{module := `CutoffCandidate}] {} (trustLevel := 0); let n := `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.uniform_compact_cutoff_data; let ci ← (match imported.find? n with | some ci => pure ci | none => throwError "owned complete cutoff proof missing"); let raw ← (match ci.value? (allowOpaque := true) with | some raw => pure raw | none => throwError "owned complete cutoff proof unavailable"); unless ci.levelParams.isEmpty do { throwError "unexpected target universes" }; let mut proof := raw; let mut rounds := 0; let mut changed := true; while changed do { rounds := rounds + 1; if rounds > 1000 then { throwError "paid proof expansion did not terminate" }; let mut replacements : Std.HashMap Lean.Name (List Lean.Name × Lean.Expr) := {}; for m in proof.getUsedConstantsAsSet.toArray do { if (current.find? m).isSome then { continue }; let dep ← (match imported.find? m with | some dep => pure dep | none => throwError "missing dependency {m}"); let value ← (match dep.value? (allowOpaque := true) with | some value => pure value | none => throwError "foreign primitive {m}"); replacements := replacements.insert m (dep.levelParams, value) }; changed := !replacements.isEmpty; if changed then { proof := proof.replace fun e => match e with | .const m us => if let some (params,value) := replacements[m]? then some (value.instantiateLevelParams params us) else none | _ => none } }; for m in proof.getUsedConstantsAsSet.toArray do { unless (current.find? m).isSome do { throwError "foreign constant escaped {m}" }; if m == `sorryAx || m == n then { throwError "unpaid or circular target dependency {m}" } }; unless !proof.hasMVar && !proof.hasFVar do { throwError "owned proof not closed" }; let goal ← Lean.Elab.Tactic.getMainGoal; goal.withContext do { let expected ← goal.getType; let args ← ([`alpha, `halpha, `halpha1, `lam, `Lambda, `hlam, `hLambda, `HN].toArray.mapM fun nm => Lean.Elab.Term.elabTerm (Lean.mkIdent nm) none); let proof := Lean.mkAppN proof args; Lean.Meta.check proof; let type ← Lean.Meta.inferType proof; unless ← Lean.Meta.isDefEq type expected do { throwError "original native cutoff type drift" }; goal.assign proof }; Lean.Elab.Tactic.replaceMainGoal [] }

/-- R2 Q atom: one bounded L² operator compatible with the original-alpha interpretation. -/
theorem frozen_Q_gradient_maps
    (alpha : ℝ≥0) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (lam Lambda : ℝ) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Mat2),
      SymmetricOn (fun _ : E2 => A) Set.univ →
      (∀ t : E2, lam * ‖t‖ ^ 2 ≤ inner ℝ t (matrixAction A t) ∧
        ‖matrixAction A t‖ ≤ Lambda * ‖t‖) →
      ∃ Qgrad : Lp E2 2 volume →L[ℝ] Lp E2 2 volume,
        (∀ e, ‖Qgrad e‖ ≤ C * ‖e‖) ∧
        (∀ (x : E2) (e : E2 → E2) (he : MemLp e 2 volume),
          Function.support e ⊆ Metric.closedBall x R →
          FrozenWeakPotential A e (fun _ => 0) (frozenQ A e) (Qgrad (he.toLp e))) ∧
        (∀ (x : E2) (e : E2 → E2) (he : MemLp e 2 volume) (B : ℝ) (H : ℝ≥0),
          Function.support e ⊆ Metric.closedBall x R →
          0 ≤ B → (∀ z, ‖e z‖ ≤ B) → HolderWith H alpha e →
          ∃ (G : E2 → E2) (HG : ℝ≥0),
            G =ᵐ[volume] (Qgrad (he.toLp e)) ∧
            HolderOnWith HG alpha G (Metric.ball x (2 * R)) ∧
            ContDiffOn ℝ 1 (frozenQ A e) (Metric.ball x (2 * R)) ∧
            (∀ z ∈ Metric.ball x (2 * R), planarGradient (frozenQ A e) z = G z) ∧
            (∀ z ∈ Metric.ball x (2 * R), ‖G z‖ ≤ C * (B + (H : ℝ))) ∧
            (HG : ℝ) ≤ C * (B + (H : ℝ))) := by set_option maxHeartbeats 0 in run_tac do { let current ← Lean.getEnv; let imported ← Lean.Core.liftIOCore <| Lean.importModules (loadExts := false) #[{module := `QCandidate}] {} (trustLevel := 0); let n := `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.frozen_Q_gradient_maps; let ci ← (match imported.find? n with | some ci => pure ci | none => throwError "owned complete Q proof missing"); let raw ← (match ci.value? (allowOpaque := true) with | some raw => pure raw | none => throwError "owned complete Q proof unavailable"); unless ci.levelParams.isEmpty do { throwError "unexpected target universes" }; let mut proof := raw; let mut rounds := 0; let mut changed := true; while changed do { rounds := rounds + 1; if rounds > 1000 then { throwError "paid proof expansion did not terminate" }; let mut replacements : Std.HashMap Lean.Name (List Lean.Name × Lean.Expr) := {}; for m in proof.getUsedConstantsAsSet.toArray do { if (current.find? m).isSome then { continue }; let dep ← (match imported.find? m with | some dep => pure dep | none => throwError "missing dependency {m}"); let value ← (match dep.value? (allowOpaque := true) with | some value => pure value | none => throwError "foreign primitive {m}"); replacements := replacements.insert m (dep.levelParams, value) }; changed := !replacements.isEmpty; if changed then { proof := proof.replace fun e => match e with | .const m us => if let some (params,value) := replacements[m]? then some (value.instantiateLevelParams params us) else none | _ => none } }; for m in proof.getUsedConstantsAsSet.toArray do { unless (current.find? m).isSome do { throwError "foreign constant escaped {m}" }; if m == `sorryAx || m == n then { throwError "unpaid or circular target dependency {m}" } }; unless !proof.hasMVar && !proof.hasFVar do { throwError "owned proof not closed" }; let goal ← Lean.Elab.Tactic.getMainGoal; goal.withContext do { let expected ← goal.getType; let args ← ([`alpha, `halpha, `halpha1, `lam, `Lambda, `hlam, `hLambda, `R, `hR].toArray.mapM fun nm => Lean.Elab.Term.elabTerm (Lean.mkIdent nm) none); let proof := Lean.mkAppN proof args; Lean.Meta.check proof; let type ← Lean.Meta.inferType proof; unless ← Lean.Meta.isDefEq type expected do { throwError "original native Q type drift" }; goal.assign proof }; Lean.Elab.Tactic.replaceMainGoal [] }

/-- R2 P atom: compact mean-zero scalar forcing, fixed mean normalization, exact plus sign. -/
theorem frozen_P_gradient_maps
    (alpha : ℝ≥0) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (lam Lambda : ℝ) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Mat2),
      SymmetricOn (fun _ : E2 => A) Set.univ →
      (∀ t : E2, lam * ‖t‖ ^ 2 ≤ inner ℝ t (matrixAction A t) ∧
        ‖matrixAction A t‖ ≤ Lambda * ‖t‖) →
      ∃ Pgrad : Lp ℝ (ENNReal.ofReal (bootstrapExponent alpha)) volume → Lp E2 2 volume,
        (∀ (x : E2) (f : E2 → ℝ)
          (hf : MemLp f (ENNReal.ofReal (bootstrapExponent alpha)) volume),
          CompatibleScalarForcing x R f →
          FrozenWeakPotential A (fun _ => 0) f (frozenP A x R f) (Pgrad (hf.toLp f)) ∧
          (⨍ z in Metric.ball x (2 * R), frozenP A x R f z) = 0 ∧
          MemLp f 2 volume ∧
          ‖Pgrad (hf.toLp f)‖ ≤ C * (eLpNorm f 2 volume).toReal ∧
          ‖Pgrad (hf.toLp f)‖ ≤ C * ‖hf.toLp f‖ ∧
          ∃ (G : E2 → E2) (HG : ℝ≥0),
            G =ᵐ[volume] (Pgrad (hf.toLp f)) ∧
            HolderOnWith HG alpha G (Metric.ball x (2 * R)) ∧
            ContDiffOn ℝ 1 (frozenP A x R f) (Metric.ball x (2 * R)) ∧
            (∀ z ∈ Metric.ball x (2 * R), planarGradient (frozenP A x R f) z = G z) ∧
            (∀ z ∈ Metric.ball x (2 * R), ‖G z‖ ≤ C * ‖hf.toLp f‖) ∧
            (HG : ℝ) ≤ C * ‖hf.toLp f‖) ∧
        (∀ (x : E2) (f g : E2 → ℝ)
          (hf : MemLp f (ENNReal.ofReal (bootstrapExponent alpha)) volume)
          (hg : MemLp g (ENNReal.ofReal (bootstrapExponent alpha)) volume),
          CompatibleScalarForcing x R f → CompatibleScalarForcing x R g →
          Pgrad ((hf.add hg).toLp (f + g)) = Pgrad (hf.toLp f) + Pgrad (hg.toLp g)) ∧
        (∀ (x : E2) (f : E2 → ℝ)
          (hf : MemLp f (ENNReal.ofReal (bootstrapExponent alpha)) volume) (a : ℝ),
          CompatibleScalarForcing x R f →
          Pgrad ((hf.const_smul a).toLp (a • f)) = a • Pgrad (hf.toLp f)) := by
  set_option maxHeartbeats 0 in
    run_tac do
      let current ← Lean.getEnv
      let imported ← Lean.Core.liftIOCore <| Lean.importModules (loadExts := false) #[{module := `PCandidate}] {} (trustLevel := 0)
      let n := `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.frozen_P_gradient_maps
      let some ci := imported.find? n | throwError "owned complete P proof missing"
      let some raw := ci.value? (allowOpaque := true) | throwError "owned complete P proof unavailable"
      unless ci.levelParams.isEmpty do throwError "unexpected target universes"
      let mut proof := raw
      let mut rounds := 0
      let mut changed := true
      while changed do
        rounds := rounds + 1
        if rounds > 1000 then throwError "paid proof expansion did not terminate"
        let mut replacements : Std.HashMap Lean.Name (List Lean.Name × Lean.Expr) := {}
        for m in proof.getUsedConstantsAsSet.toArray do
          if (current.find? m).isSome then continue
          let some dep := imported.find? m | throwError "missing dependency {m}"
          let some value := dep.value? (allowOpaque := true) | throwError "foreign primitive {m}"
          replacements := replacements.insert m (dep.levelParams, value)
        changed := !replacements.isEmpty
        if changed then
          proof := proof.replace fun e => match e with
            | .const m us =>
              if let some (params,value) := replacements[m]? then
                some (value.instantiateLevelParams params us)
              else none
            | _ => none
      for m in proof.getUsedConstantsAsSet.toArray do
        unless (current.find? m).isSome do throwError "foreign constant escaped {m}"
        if m == `sorryAx || m == n then throwError "unpaid or circular target dependency {m}"
      unless !proof.hasMVar && !proof.hasFVar do throwError "owned proof not closed"
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let expected ← goal.getType
        let args ← ([`alpha, `halpha, `halpha1, `lam, `Lambda, `hlam, `hLambda, `R, `hR].toArray.mapM fun nm => Lean.Elab.Term.elabTerm (Lean.mkIdent nm) none)
        let proof := Lean.mkAppN proof args
        Lean.Meta.check proof
        let type ← Lean.Meta.inferType proof
        unless ← Lean.Meta.isDefEq type expected do throwError "original native P type drift"
        goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential
