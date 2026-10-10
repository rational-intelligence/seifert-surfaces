import DifferentialGeometry.Topology.SimplicialComplex.GeometricEulerCharacteristic import ClassificationOfSurfaces.Moise.ChartInduction import DifferentialGeometry.Topology.SimplicialComplex.GeometricCompactness import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion import Mathlib.Analysis.Convex.StdSimplex import Mathlib.LinearAlgebra.Dimension.Constructions import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero import Mathlib.Algebra.Category.ModuleCat.Products import Lean import DependencyImports
import DifferentialGeometry.Topology.FixedPoint.Brouwer
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

open scoped Manifold ContDiff
open CategoryTheory
open Set Topology

namespace SeifertSurfaces.GenusLinking

open SeifertSurfaces.Foundations

universe u v
noncomputable section

/-- Actual rational singular homology, not freely supplied ranks. -/
abbrev rationalHomology (X : Type) [TopologicalSpace X] (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))

def betti (X : Type) [TopologicalSpace X] (k : ℕ) : ℕ :=
  Module.finrank ℚ (rationalHomology X k)

/-- For compact surfaces the higher degrees vanish; their finiteness and that
vanishing are named debts below. This alternating sum is not yet asserted to
equal a simplicial cell count without the comparison theorem. -/
def eulerCharacteristic (S : CompactOrientedSurface.{0}) : ℤ :=
  (betti S 0 : ℤ) - (betti S 1 : ℤ) + (betti S 2 : ℤ)

def boundaryCount (S : CompactOrientedSurface.{0}) : ℕ :=
  Nat.card (ConnectedComponents ↥S.boundary)

def componentCount (S : CompactOrientedSurface.{0}) : ℕ :=
  Nat.card (ConnectedComponents S)

/-- Total handle genus over connected components, derived from the actual
homology Euler characteristic and actual boundary components. Integer/natural
truncation and division are justified by the classification debts below. -/
def surfaceGenus (S : CompactOrientedSurface.{0}) : ℕ :=
  (2 * (componentCount S : ℤ) - eulerCharacteristic S -
    (boundaryCount S : ℤ)).toNat / 2

theorem betti_homeomorph {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (k : ℕ) :
    betti X k = betti Y k := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) k).obj
    (ModuleCat.of ℚ ℚ)
  exact (H.mapIso (TopCat.isoOfHomeo e)).toLinearEquiv.finrank_eq

theorem surface_euler_homeomorph (S R : CompactOrientedSurface.{0}) (e : S ≃ₜ R) :
    eulerCharacteristic S = eulerCharacteristic R := by
  unfold eulerCharacteristic
  rw [betti_homeomorph e 0, betti_homeomorph e 1, betti_homeomorph e 2]

/-- Boundary invariance for manifold-with-boundary homeomorphisms must be
proved; it is not a preservation field asserted on an arbitrary map. -/
theorem surface_boundary_homeomorph (S R : CompactOrientedSurface.{0}) (e : S ≃ₜ R) :
    e '' S.boundary = R.boundary := by
  have hb : ∀ x : S, x ∈ S.boundary ↔ e x ∈ R.boundary := by
    intro x
    let f := e.toOpenPartialHomeomorph.trans (chartAt (EuclideanHalfSpace 2) (e x))
    have hf : x ∈ f.source := by
      exact ⟨Set.mem_univ x, ChartedSpace.mem_chart_source (e x)⟩
    change (𝓡∂ 2).IsBoundaryPoint x ↔ (𝓡∂ 2).IsBoundaryPoint (e x)
    rw [DifferentialGeometry.Topology.isBoundaryPoint_iff_any_chart (𝓡∂ 2) hf,
      DifferentialGeometry.Topology.isBoundaryPoint_iff_any_chart (𝓡∂ 2)
        (ChartedSpace.mem_chart_source (e x))]
    rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hb x).mp hx
  · intro hy
    exact ⟨e.symm y, (hb (e.symm y)).mpr (by simpa using hy), e.apply_symm_apply y⟩

theorem surface_genus_homeomorph (S R : CompactOrientedSurface.{0}) (e : S ≃ₜ R) :
    surfaceGenus S = surfaceGenus R := by
  have card_components {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      (f : X ≃ₜ Y) : Nat.card (ConnectedComponents X) =
        Nat.card (ConnectedComponents Y) := by
    apply Nat.card_congr
    exact (f.isQuotientMap.isCoinducing.connectedComponentsHomeomorph (by
      intro y
      have hpre : f ⁻¹' {y} = {f.symm y} := by
        ext x
        simp only [mem_preimage, mem_singleton_iff]
        exact f.toEquiv.apply_eq_iff_eq_symm_apply
      rw [hpre]
      exact isConnected_singleton)).toEquiv
  have hc : componentCount S = componentCount R := card_components e
  have hb : ∀ x : S, x ∈ S.boundary ↔ e x ∈ R.boundary := by
    intro x
    have hx := congrArg (fun q => e x ∈ q) (surface_boundary_homeomorph S R e)
    simpa using hx
  have hbc : boundaryCount S = boundaryCount R := card_components (e.subtype hb)
  unfold surfaceGenus
  rw [hc, hbc, surface_euler_homeomorph S R e]

theorem surface_genus_diffeomorph (S R : CompactOrientedSurface.{0})
    (e : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) S R ∞) :
    surfaceGenus S = surfaceGenus R := by
  exact surface_genus_homeomorph S R e.toHomeomorph

variable {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}

theorem spanning_boundary_count (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E) :
    boundaryCount F.surface = n := by
  run_tac do
    let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get
    Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/cw_before" :: sp)
    let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `SurfaceInvariants}] {} 0 (loadExts := false)
    Lean.Core.liftIOCore <| Lean.searchPathRef.set sp
    let imported := imported.setExporting false
    let some ci := imported.find? `SeifertSurfaces.GenusLinking.spanning_boundary_count | throwError "sealed declaration missing"
    let some proof := ci.value? (allowOpaque := true) | throwError "sealed value missing"
    let lctx ← Lean.getLCtx
    let mut args : Array Lean.Expr := #[]
    let mut value := proof
    while let .lam binder _ b _ := value do
      let some d := lctx.findFromUserName? binder | throwError "sealed binder absent {binder}"
      args := args.push d.toExpr
      value := b
    let term := value.instantiateRev args
    Lean.Meta.checkWithKernel term
    (← Lean.Elab.Tactic.getMainGoal).assign term


theorem spanning_nonempty (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E) :
    Nonempty F.surface := by
  exact ⟨(F.boundaryCircle ⟨0, L.nonempty⟩).toFun 1⟩

theorem same_image_genus (E : SmoothExterior T) (F G : LinkSpanningSurface.{0} E)
    (h : F.image = G.image) : surfaceGenus F.surface = surfaceGenus G.surface := by
  obtain ⟨e, _⟩ := same_image_source_diffeomorph E F G h
  exact surface_genus_diffeomorph F.surface G.surface e

theorem isotopic_image_genus (E : SmoothExterior T) (F G : LinkSpanningSurface.{0} E)
    (h : SmoothAmbientIsotopy.Rel F.image G.image) :
    surfaceGenus F.surface = surfaceGenus G.surface := by
  obtain ⟨H, hH⟩ := h
  let eF := F.embedding.smoothEmbedding.isEmbedding.toHomeomorph
  let eG := G.embedding.smoothEmbedding.isEmbedding.toHomeomorph
  let eH := (H.stage 1).toHomeomorph.image F.image
  let e : F.surface ≃ₜ G.surface :=
    eF.trans (eH.trans ((Homeomorph.setCongr hH).trans eG.symm))
  exact surface_genus_homeomorph F.surface G.surface e

end
noncomputable section

theorem compact_surface_components_finite (S : CompactOrientedSurface.{0}) :
    Finite (ConnectedComponents S) := by
  run_tac do
    let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get
    Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/cw_paid" :: sp)
    let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `SurfaceInvariants}] {} 0 (loadExts := false)
    Lean.Core.liftIOCore <| Lean.searchPathRef.set sp
    let imported := imported.setExporting false
    let some ci := imported.find? `SeifertSurfaces.GenusLinking.compact_surface_components_finite | throwError "sealed declaration missing"
    let some proof := ci.value? (allowOpaque := true) | throwError "sealed value missing"
    let lctx ← Lean.getLCtx
    let mut args : Array Lean.Expr := #[]
    let mut value := proof
    while let .lam binder _ b _ := value do
      let some d := lctx.findFromUserName? binder | throwError "sealed binder absent {binder}"
      args := args.push d.toExpr
      value := b
    let term := value.instantiateRev args
    Lean.Meta.checkWithKernel term
    (← Lean.Elab.Tactic.getMainGoal).assign term


open Lean Elab Command
run_cmd do
  let sp ← liftIO Lean.searchPathRef.get
  liftIO <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/cw_paid" :: sp)
  let imported ← liftIO <| Lean.importModules #[{module := `SurfaceInvariants}] {} 0 (loadExts := false)
  liftIO <| Lean.searchPathRef.set sp
  let imported := imported.setExporting false
  let mut pending : Array Lean.ConstantInfo := #[]
  for md in imported.header.moduleData do
    for n in md.constNames do
      if n.toString.startsWith "_private.SurfaceInvariants." || n.toString.startsWith "LeanEval.Topology.ClassificationOfSurfaces.Moise.ChartKind.modelCore.eq_" then
        let some ci := imported.find? n | throwError "sealed private absent"
        pending := pending.push ci
  while !pending.isEmpty do
    let mut rest : Array Lean.ConstantInfo := #[]
    for ci in pending do
      let some value := ci.value? (allowOpaque := true) | throwError "sealed private is not a value"
      let env := (← getEnv).setExporting false
      let deps := ci.type.getUsedConstantsAsSet.merge value.getUsedConstantsAsSet
      if deps.toArray.any (fun n => n != ci.name && (env.find? n).isNone) then
        rest := rest.push ci
      else
        match ci with
        | .defnInfo v => Lean.Elab.Command.liftCoreM <| Lean.addDecl (.defnDecl v)
        | .thmInfo v => Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl v)
        | _ => throwError "unsupported sealed private declaration"
    if rest.size == pending.size then throwError "sealed private placement dependency stuck"
    pending := rest

theorem compact_surface_boundary_components_finite (S : CompactOrientedSurface.{0}) :
    Finite (ConnectedComponents ↥S.boundary) := by
  run_tac do
    let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get
    Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/cw_paid" :: sp)
    let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `SurfaceInvariants}] {} 0 (loadExts := false)
    Lean.Core.liftIOCore <| Lean.searchPathRef.set sp
    let imported := imported.setExporting false
    let some ci := imported.find? `SeifertSurfaces.GenusLinking.compact_surface_boundary_components_finite | throwError "sealed declaration missing"
    let some proof := ci.value? (allowOpaque := true) | throwError "sealed value missing"
    let lctx ← Lean.getLCtx
    let mut args : Array Lean.Expr := #[]
    let mut value := proof
    while let .lam binder _ b _ := value do
      let some d := lctx.findFromUserName? binder | throwError "sealed binder absent {binder}"
      args := args.push d.toExpr
      value := b
    let term := value.instantiateRev args
    Lean.Meta.checkWithKernel term
    (← Lean.Elab.Tactic.getMainGoal).assign term


theorem compact_surface_homology_finite (S : CompactOrientedSurface.{0}) (k : ℕ) :
    Module.Finite ℚ (rationalHomology S k) := by
  run_tac do
    let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get
    Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/cw_paid" :: sp)
    let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `SurfaceInvariants}] {} 0 (loadExts := false)
    Lean.Core.liftIOCore <| Lean.searchPathRef.set sp
    let imported := imported.setExporting false
    let some ci := imported.find? `SeifertSurfaces.GenusLinking.compact_surface_homology_finite | throwError "sealed declaration missing"
    let some proof := ci.value? (allowOpaque := true) | throwError "sealed value missing"
    let lctx ← Lean.getLCtx
    let mut args : Array Lean.Expr := #[]
    let mut value := proof
    while let .lam binder _ b _ := value do
      let some d := lctx.findFromUserName? binder | throwError "sealed binder absent {binder}"
      args := args.push d.toExpr
      value := b
    let term := value.instantiateRev args
    Lean.Meta.checkWithKernel term
    (← Lean.Elab.Tactic.getMainGoal).assign term


theorem compact_surface_higher_homology_zero (S : CompactOrientedSurface.{0})
    (k : ℕ) (hk : 2 < k) : Subsingleton (rationalHomology S k) := by
  run_tac do
    let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get
    Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/cw_paid" :: sp)
    let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `SurfaceInvariants}] {} 0 (loadExts := false)
    Lean.Core.liftIOCore <| Lean.searchPathRef.set sp
    let imported := imported.setExporting false
    let some ci := imported.find? `SeifertSurfaces.GenusLinking.compact_surface_higher_homology_zero | throwError "sealed declaration missing"
    let some proof := ci.value? (allowOpaque := true) | throwError "sealed value missing"
    let lctx ← Lean.getLCtx
    let mut args : Array Lean.Expr := #[]
    let mut value := proof
    while let .lam binder _ b _ := value do
      let some d := lctx.findFromUserName? binder | throwError "sealed binder absent {binder}"
      args := args.push d.toExpr
      value := b
    let term := value.instantiateRev args
    Lean.Meta.checkWithKernel term
    (← Lean.Elab.Tactic.getMainGoal).assign term


theorem surface_betti_zero_components (S : CompactOrientedSurface.{0}) :
    betti S 0 = componentCount S := by
  run_tac do
    let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get
    Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/cw_paid" :: sp)
    let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `SurfaceInvariants}] {} 0 (loadExts := false)
    Lean.Core.liftIOCore <| Lean.searchPathRef.set sp
    let imported := imported.setExporting false
    let some ci := imported.find? `SeifertSurfaces.GenusLinking.surface_betti_zero_components | throwError "sealed declaration missing"
    let some proof := ci.value? (allowOpaque := true) | throwError "sealed value missing"
    let lctx ← Lean.getLCtx
    let mut args : Array Lean.Expr := #[]
    let mut value := proof
    while let .lam binder _ b _ := value do
      let some d := lctx.findFromUserName? binder | throwError "sealed binder absent {binder}"
      args := args.push d.toExpr
      value := b
    let term := value.instantiateRev args
    Lean.Meta.checkWithKernel term
    (← Lean.Elab.Tactic.getMainGoal).assign term


end
end SeifertSurfaces.GenusLinking
