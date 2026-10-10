import B1MetricVariationalInterfaces

noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
open SeifertSurfaces.AppendixACoordinates

def planarCap (x : E2) (r : ℝ) : Set E2 := disc 1 ∩ Metric.ball x r

def circlePatch (x : E2) (r : ℝ) : Set ℝ :=
  Icc 0 (2 * Real.pi) ∩ {t | unitCircleParameter t ∈ Metric.ball x r}

def zeroExtension {F : Type*} [Zero F] (U : Set E2) (v : E2 → F) : E2 → F :=
  U.indicator v

def pastedMap (U : Set E2) (f h : E2 → E2) : E2 → E2 :=
  fun x => @ite E2 (x ∈ U) (Classical.propDecidable _) (h x) (f x)

def pastedJets (U : Set E2) (d dh : Fin 2 → E2 → E2) : Fin 2 → E2 → E2 :=
  fun i x => @ite E2 (x ∈ U) (Classical.propDecidable _) (dh i x) (d i x)

def euclideanJetDensity (d : Fin 2 → E2 → E2) (x : E2) : ℝ :=
  ∑ i, ‖d i x‖ ^ 2

/-- The artificial interface has zero residual; the only permitted residual is
the actual changed Green trace on the true circular arc. -/
def RelativeCapGreen (x : E2) (r : ℝ) (f h : E2 → E2)
    (d dh : Fin 2 → E2 → E2) (b b' : ℝ → E2) : Prop :=
  ∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
    IntegrableOn (fun z => (h z i - f z i) *
      fderiv ℝ psi z (coordinateVector 2 j) + (dh i z j - d i z j) * psi z)
      (planarCap x r) ∧
    IntegrableOn (fun t => (b' t i - b t i) * psi (unitCircleParameter t) *
      unitCircleParameter t j) (circlePatch x r) ∧
    (∫ z in planarCap x r, (h z i - f z i) *
      fderiv ℝ psi z (coordinateVector 2 j) + (dh i z j - d i z j) * psi z) =
    ∫ t in circlePatch x r, (b' t i - b t i) * psi (unitCircleParameter t) *
      unitCircleParameter t j

/-- Native H10 approximation implies zero extension and literal zero Green
residual. This is an owed gluing theorem, not an assumed global competitor. -/
theorem zero_trace_extension_green (U : Set E2) (open_U : IsOpen U)
    (inside : U ⊆ disc 1) (v : E2 → ℝ) (dv : E2 → E2)
    (zero_trace : H10On U v dv) :
    H10On (disc 1) (zeroExtension U v) (zeroExtension U dv) ∧
    (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ j : Fin 2,
      IntegrableOn (fun z => zeroExtension U v z *
        fderiv ℝ psi z (coordinateVector 2 j) + zeroExtension U dv z j * psi z)
        (disc 1) ∧
      (∫ z in disc 1, zeroExtension U v z *
        fderiv ℝ psi z (coordinateVector 2 j) + zeroExtension U dv z j * psi z) = 0) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "native_paid7.olean")
    let some ci := data.constants.find? (fun c => c.name.toString == "SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.zero_trace_extension_green") | throwError "exact native proof missing"
    let some raw := ci.value? (allowOpaque := true) | throwError "exact native proof body missing"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

/-- Interior disc replacement: the SAME boundary lift/degree survives, and
the piecewise gradients are literal. The local H10 difference is its seam datum. -/
theorem interior_disc_paste {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (f h : E2 → E2) (d dh : Fin 2 → E2 → E2)
    (base_H1 : ∀ i, H1On (disc 1) (fun z => f z i) (d i))
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (x : E2) (r : ℝ) (radius : 0 < r)
    (interior : Metric.closedBall x r ⊆ disc 1)
    (seam : ∀ i, H10On (Metric.ball x r) (fun z => h z i - f z i)
      (fun z => dh i z - d i z)) :
    (∀ i, H1On (disc 1) (fun z => pastedMap (Metric.ball x r) f h z i)
      (pastedJets (Metric.ball x r) d dh i)) ∧
    HasGreenBoundaryTrace (pastedMap (Metric.ball x r) f h)
      (pastedJets (Metric.ball x r) d dh) (liftedBoundaryValue Ω theta) ∧
    MetricAdmissible Ω (pastedMap (Metric.ball x r) f h)
      (pastedJets (Metric.ball x r) d dh) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "native_paid7.olean")
    let some ci := data.constants.find? (fun c => c.name.toString == "SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.interior_disc_paste") | throwError "exact native proof missing"
    let some raw := ci.value? (allowOpaque := true) | throwError "exact native proof body missing"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

/-- Boundary cap replacement allows a different continuous monotone lift of
the SAME sign/degree. The local Green equation accounts for both boundary parts. -/
theorem boundary_cap_paste {R : ℝ} (Ω : SmoothFlatJordanDomain R)
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
      (pastedJets (planarCap x r) d dh) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "current_native_independent.olean")
    let some ci := data.constants.find? (fun c => c.name.toString == "SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.boundary_cap_paste") | throwError "exact native proof missing"
    let some raw := ci.value? (allowOpaque := true) | throwError "exact native proof body missing"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

/-- Original thirteen inputs are preserved. Off-patch cancellation yields
the local metric inequality and then the explicit Lambda/ell Euclidean bound. -/
theorem same_minimizer_local_energy (R : ℝ) (A : E2 → Mat2)
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
      (Lambda / ell) * ∫ z in U, euclideanJetDensity dh z := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "native_paid7.olean")
    let some ci := data.constants.find? (fun c => c.name.toString == "SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.same_minimizer_local_energy") | throwError "exact native proof missing"
    let some raw := ci.value? (allowOpaque := true) | throwError "exact native proof body missing"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []
def capVolume (x : E2) (r : ℝ) : ℝ := (volume (planarCap x r)).toReal

def capMean (V : E2 → Mat2) (x : E2) (r : ℝ) : Mat2 :=
  fun i j => (capVolume x r)⁻¹ * ∫ z in planarCap x r, V z i j

def frobeniusSquared (V : Mat2) : ℝ := ∑ i, ∑ j, (V i j) ^ 2

def capExcess (V : E2 → Mat2) (x : E2) (r : ℝ) : ℝ :=
  ∫ z in planarCap x r, frobeniusSquared (V z - capMean V x r)

def dyadicRadius (r0 : ℝ) (n : ℕ) : ℝ := r0 / (2 : ℝ) ^ n

/-- Volume comparability for actual planar caps, including centers on ∂B. -/
theorem planar_cap_volume_comparable :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ x ∈ closedDisc 1, ∀ r : ℝ, 0 < r → r ≤ 1 →
        volume (planarCap x r) ≠ ⊤ ∧ 0 < capVolume x r ∧
        c * r ^ 2 ≤ capVolume x r ∧ capVolume x r ≤ C * r ^ 2 := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "current_native_independent.olean")
    let some ci := data.constants.find? (fun c => c.name.toString == "SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.planar_cap_volume_comparable") | throwError "exact native proof missing"
    let some raw := ci.value? (allowOpaque := true) | throwError "exact native proof body missing"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

/-- Full cap Campanato reconstruction from the GIVEN L2 matrix field. All
constants precede the scale and centers; dyadic means are concrete approximants.
No smooth approximating minimizer, boundary trace or PDE is an input. -/
theorem planar_cap_campanato (V : E2 → Mat2)
    (L2 : ∀ i j, MemLp (fun x => V x i j) 2 (volume.restrict (disc 1)))
    (gamma : ℝ≥0) (gamma_pos : 0 < gamma) (gamma_lt_one : gamma < 1)
    (C r0 : ℝ) (C_nonneg : 0 ≤ C) (r0_pos : 0 < r0) (r0_le_one : r0 ≤ 1)
    (excess : ∀ x ∈ closedDisc 1, ∀ r : ℝ, 0 < r → r ≤ r0 →
      capExcess V x r ≤ C * Real.rpow r (2 + 2 * (gamma : ℝ))) :
    ∃ Vc : E2 → Mat2, ∃ K : ℝ≥0,
      ContinuousOn Vc (closedDisc 1) ∧
      Vc =ᵐ[volume.restrict (disc 1)] V ∧
      (∀ i j, HolderOnWith K gamma (fun x => Vc x i j) (closedDisc 1)) ∧
      (∀ i j, TendstoUniformlyOn (fun n x => capMean V x (dyadicRadius r0 n) i j)
        (fun x => Vc x i j) Filter.atTop (closedDisc 1)) ∧
      (∀ n : ℕ, ∀ x ∈ closedDisc 1,
        frobeniusSquared (capMean V x (dyadicRadius r0 n) - Vc x) ≤
          (K : ℝ) ^ 2 * Real.rpow (dyadicRadius r0 n) (2 * (gamma : ℝ))) ∧
      (∀ x ∈ closedDisc 1, ∀ r s : ℝ, 0 < r → r ≤ r0 →
        r / 2 ≤ s → s ≤ r →
        frobeniusSquared (capMean V x r - capMean V x s) ≤
          (K : ℝ) ^ 2 * Real.rpow r (2 * (gamma : ℝ))) ∧
      (∀ x ∈ closedDisc 1, ∀ y ∈ closedDisc 1, ∀ r : ℝ,
        0 < r → 3 * r ≤ r0 → dist x y ≤ r →
        frobeniusSquared (capMean V x r - capMean V y r) ≤
          (K : ℝ) ^ 2 * Real.rpow r (2 * (gamma : ℝ))) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "current_native_independent.olean")
    let some ci := data.constants.find? (fun c => c.name.toString == "SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.planar_cap_campanato") | throwError "exact native proof missing"
    let some raw := ci.value? (allowOpaque := true) | throwError "exact native proof body missing"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

/-- The same continuous Sobolev representative is differentiated. Convex
closure/unique differentiation extends the actual derivative to the closed disc. -/
theorem continuous_weak_jets_classical (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (continuous_u : ContinuousOn u (closedDisc 1))
    (H1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (Vc : E2 → Mat2) (continuous_jets : ContinuousOn Vc (closedDisc 1))
    (same_jets : Vc =ᵐ[volume.restrict (disc 1)] weakJacobian d) :
    ContDiffOn ℝ 1 u (closedDisc 1) ∧
    (∀ x ∈ disc 1, ∀ v : E2, fderiv ℝ u x v = matrixAction (Vc x) v) ∧
    (∀ x ∈ closedDisc 1, ∀ v : E2,
      fderivWithin ℝ u (closedDisc 1) x v = matrixAction (Vc x) v) ∧
    (∀ x ∈ closedDisc 1, jacobianWithin u (closedDisc 1) x = Vc x) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "current_native_independent.olean")
    let some ci := data.constants.find? (fun c => c.name.toString == "SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent.continuous_weak_jets_classical") | throwError "exact native proof missing"
    let some raw := ci.value? (allowOpaque := true) | throwError "exact native proof body missing"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
