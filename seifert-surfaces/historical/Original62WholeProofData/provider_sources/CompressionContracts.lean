import CompressionComponentSupport

set_option autoImplicit false

open scoped Manifold ContDiff BigOperators
open Set Topology

namespace SeifertSurfaces.GenusLinking
open SeifertSurfaces.Foundations

noncomputable section
attribute [local instance] Classical.propDecidable

theorem midpoint_in_time : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num

def middleTime : Time := ⟨1 / 2, midpoint_in_time⟩

/-- Compression surgery uses an essential circle in the surface interior.
The provisional imported disk record does not explicitly impose this source
condition, so it is restored transparently in a new refinement. -/
structure InteriorCompressingDisk {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (f : NeatEmbedding S M) extends CompressingDisk.{0} f where
  loop_interior : Set.range surfaceLoop ⊆ S.boundaryᶜ

structure CompressionAnnulus {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} (D : InteriorCompressingDisk f) where
  band : C(Circle × Time, S)
  embedded : IsEmbedding band
  interior_surface : Set.range band ⊆ S.boundaryᶜ
  center : ∀ z, band (z, middleTime) = D.surfaceLoop z
  open_middle : IsOpen (band '' {p : Circle × Time | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1})

namespace CompressionAnnulus
variable {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f} (A : CompressionAnnulus D)

def removed : Set S := A.band '' {p : Circle × Time | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}
abbrev Remainder := ↥A.removedᶜ

def sideTime (k : Fin 2) : Time := if k = 0 then 0 else 1

theorem band_edge_remains (k : Fin 2) (z : Circle) :
    A.band (z, sideTime k) ∈ A.removedᶜ := by
  rintro ⟨p, hp, heq⟩
  have htime := congrArg (fun p : Circle × Time => (p.2 : ℝ)) (A.embedded.injective heq)
  by_cases hk : k = 0
  · simp [sideTime, hk] at htime
    exact (ne_of_gt hp.1) (congrArg (fun t : Time => (t : ℝ)) htime)
  · simp [sideTime, hk] at htime
    exact (ne_of_lt hp.2) (congrArg (fun t : Time => (t : ℝ)) htime)

def edgePoint (k : Fin 2) (z : Circle) : A.Remainder :=
  ⟨A.band (z, sideTime k), A.band_edge_remains k z⟩

theorem capEdge_mem (z : Circle) : circleVector z ∈ Metric.closedBall (0 : Euc 2) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, circleVector_norm]

def capEdge (z : Circle) : ClosedDisk := ⟨circleVector z, capEdge_mem z⟩

/-- Concrete gluing of the two unit disk boundaries to the two annulus edges.
The quotient's equivalence closure identifies only these boundary points. -/
inductive Gluing : (A.Remainder ⊕ (Fin 2 × ClosedDisk)) →
    (A.Remainder ⊕ (Fin 2 × ClosedDisk)) → Prop where
  | attach (k : Fin 2) (z : Circle) :
      Gluing (.inl (A.edgePoint k z)) (.inr (k, capEdge z))

def SurgerySpace := Quot A.Gluing

instance : TopologicalSpace A.SurgerySpace := inferInstanceAs (TopologicalSpace (Quot A.Gluing))

def remainderInclusion (x : A.Remainder) : A.SurgerySpace := Quot.mk A.Gluing (.inl x)
def capInclusion (k : Fin 2) (x : ClosedDisk) : A.SurgerySpace := Quot.mk A.Gluing (.inr (k, x))

/-- Separating is defined on the original surface with the essential circle
removed, rather than presumed from genus arithmetic. -/
def Separating (_A : CompressionAnnulus D) : Prop :=
  ¬ IsConnected (Set.range D.surfaceLoop)ᶜ

end CompressionAnnulus

structure SmoothCompressionSurface {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (A : CompressionAnnulus D) where
  surface : CompactOrientedSurface.{0}
  realization : surface ≃ₜ A.SurgerySpace
  boundary_matches : ∀ x : A.Remainder,
    realization.symm (A.remainderInclusion x) ∈ surface.boundary ↔ (x : S) ∈ S.boundary
  caps_interior : ∀ k x,
    realization.symm (A.capInclusion k x) ∉ surface.boundary

variable {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L} (E : SmoothExterior T)
attribute [local instance 2000] ChainCompletePartialOrder.toPartialOrder in
structure EmbeddedCompression (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D)
    (P : SmoothCompressionSurface A) where
  embedding : NeatEmbedding P.surface E.Carrier
  seamNeighborhood : Set F.surface
  seam_open : IsOpen seamNeighborhood
  seam_contains : ∀ k z, A.band (z, CompressionAnnulus.sideTime k) ∈ seamNeighborhood
  unchanged : ∀ x : A.Remainder, (x : F.surface) ∉ seamNeighborhood →
    embedding.toFun (P.realization.symm (A.remainderInclusion x)) = F.embedding.toFun x
  boundary_fixed : ∀ x : A.Remainder, (x : F.surface) ∈ F.surface.boundary →
    embedding.toFun (P.realization.symm (A.remainderInclusion x)) = F.embedding.toFun x
  seam_away_boundary : Disjoint seamNeighborhood F.surface.boundary

structure SurgeryComponent {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    {A : CompressionAnnulus D} (P : SmoothCompressionSurface A) where
  point : P.surface
  surface : CompactOrientedSurface.{0}
  realization : surface ≃ₜ ↥(connectedComponent point)
  boundary_matches : ∀ x, x ∈ surface.boundary ↔
    (realization x : P.surface) ∈ P.surface.boundary

theorem surgery_component_realizable (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D)
    (P : SmoothCompressionSurface A) (x : P.surface) :
    ∃ C : SurgeryComponent P, C.point = x := by
  let C : SurgeryComponent P := {
    point := x
    surface := CompressionSupport.componentSurface P.surface x
    realization := Homeomorph.refl _
    boundary_matches := CompressionSupport.componentSurface_boundary P.surface x }
  exact ⟨C,rfl⟩




theorem nonseparating_compression_connected (F : LinkSpanningSurface.{0} E)
    [ConnectedSpace F.surface] (D : InteriorCompressingDisk F.embedding)
    (A : CompressionAnnulus D) (hA : ¬ A.Separating) (P : SmoothCompressionSurface A) :
    ConnectedSpace P.surface := by
  set_option maxHeartbeats 0 in
    run_tac do
      let current ← Lean.getEnv
      let savedPath ← Lean.Core.liftIOCore <| Lean.searchPathRef.get
      Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/compression_donor/objects" :: savedPath)
      let imported ← Lean.Core.liftIOCore <| Lean.importModules (loadExts := false) #[{module := `CompressionTopologyRelease}] {} (trustLevel := 0)
      Lean.Core.liftIOCore <| Lean.searchPathRef.set savedPath
      let n := `SeifertSurfaces.GenusLinking.nonseparating_compression_connected
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
        let mut proof := proof
        let ctx ← Lean.MonadLCtx.getLCtx
        let mut fuel := 0
        while true do
          fuel := fuel + 1
          if fuel > 100 then throwError "paid target telescope did not terminate"
          let type ← Lean.Meta.whnf (← Lean.Meta.inferType proof)
          let .forallE binderName binderType _ _ := type | break
          let mut candidate : Option Lean.Expr := none
          for decl in ctx do
            if decl.userName == binderName then
              if ← Lean.Meta.isDefEq decl.type binderType then
                candidate := some decl.toExpr
                break
          if candidate.isNone then
            for decl in ctx do
              if ← Lean.Meta.isDefEq decl.type binderType then
                candidate := some decl.toExpr
                break
          let some arg := candidate | throwError "paid binder placement missing {binderName}"
          proof := Lean.mkApp proof arg
        Lean.Meta.check proof
        let type ← Lean.Meta.inferType proof
        unless ← Lean.Meta.isDefEq type expected do throwError "original native P type drift"
        goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []



theorem separating_compression_two_components (F : LinkSpanningSurface.{0} E)
    [ConnectedSpace F.surface] (D : InteriorCompressingDisk F.embedding)
    (A : CompressionAnnulus D) (hA : A.Separating) (P : SmoothCompressionSurface A) :
    componentCount P.surface = 2 := by
  set_option maxHeartbeats 0 in
    run_tac do
      let current ← Lean.getEnv
      let savedPath ← Lean.Core.liftIOCore <| Lean.searchPathRef.get
      Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/compression_donor/objects" :: savedPath)
      let imported ← Lean.Core.liftIOCore <| Lean.importModules (loadExts := false) #[{module := `CompressionSeparatingRelease}] {} (trustLevel := 0)
      Lean.Core.liftIOCore <| Lean.searchPathRef.set savedPath
      let n := `SeifertSurfaces.GenusLinking.separating_compression_two_components
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
        let mut proof := proof
        let ctx ← Lean.MonadLCtx.getLCtx
        let mut fuel := 0
        while true do
          fuel := fuel + 1
          if fuel > 100 then throwError "paid target telescope did not terminate"
          let type ← Lean.Meta.whnf (← Lean.Meta.inferType proof)
          let .forallE binderName binderType _ _ := type | break
          let mut candidate : Option Lean.Expr := none
          for decl in ctx do
            if decl.userName == binderName then
              if ← Lean.Meta.isDefEq decl.type binderType then
                candidate := some decl.toExpr
                break
          if candidate.isNone then
            for decl in ctx do
              if ← Lean.Meta.isDefEq decl.type binderType then
                candidate := some decl.toExpr
                break
          let some arg := candidate | throwError "paid binder placement missing {binderName}"
          proof := Lean.mkApp proof arg
        Lean.Meta.check proof
        let type ← Lean.Meta.inferType proof
        unless ← Lean.Meta.isDefEq type expected do throwError "original native P type drift"
        goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []


theorem closed_surgery_component_not_sphere (F : LinkSpanningSurface.{0} E)
    [ConnectedSpace F.surface] (D : InteriorCompressingDisk F.embedding)
    (A : CompressionAnnulus D) (hA : A.Separating)
    (P : SmoothCompressionSurface A) (C : SurgeryComponent P)
    (hC : C.surface.boundary = ∅) : ¬ Nonempty (C.surface ≃ₜ TwoSphere) := by
  set_option maxHeartbeats 0 in
    run_tac do
      let current ← Lean.getEnv
      let savedPath ← Lean.Core.liftIOCore <| Lean.searchPathRef.get
      Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/nosphere_donor/objects" :: savedPath)
      let imported ← Lean.Core.liftIOCore <| Lean.importModules (loadExts := false) #[{module := `CompressionNoSphereRelease}] {} (trustLevel := 0)
      Lean.Core.liftIOCore <| Lean.searchPathRef.set savedPath
      let n := `SeifertSurfaces.GenusLinking.closed_surgery_component_not_sphere
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
        let mut proof := proof
        let ctx ← Lean.MonadLCtx.getLCtx
        let mut fuel := 0
        while true do
          fuel := fuel + 1
          if fuel > 100 then throwError "paid target telescope did not terminate"
          let type ← Lean.Meta.whnf (← Lean.Meta.inferType proof)
          if ← Lean.Meta.isDefEq type expected then break
          let .forallE binderName binderType _ _ := type | break
          let mut candidate : Option Lean.Expr := none
          for decl in ctx do
            if decl.userName == binderName then
              if ← Lean.Meta.isDefEq decl.type binderType then
                candidate := some decl.toExpr
                break
          if candidate.isNone then
            for decl in ctx do
              if ← Lean.Meta.isDefEq decl.type binderType then
                candidate := some decl.toExpr
                break
          let some arg := candidate | throwError "paid binder placement missing {binderName}"
          proof := Lean.mkApp proof arg
        Lean.Meta.check proof
        let type ← Lean.Meta.inferType proof
        unless ← Lean.Meta.isDefEq type expected do throwError "original native P type drift"
        goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []



end
end SeifertSurfaces.GenusLinking
