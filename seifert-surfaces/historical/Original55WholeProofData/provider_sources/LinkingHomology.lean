import SurfaceInvariants import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereRank import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import CycleAssembly
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Piecewise
set_option autoImplicit false

open scoped Manifold ContDiff Simplicial BigOperators
open CategoryTheory Convexity
open Set Topology
attribute [-instance] CategoryTheory.catToReflQuiver
namespace SeifertSurfaces.GenusLinking
open SeifertSurfaces.Foundations

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Integral singular chains and homology of the actual space. -/
abbrev integralChains (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

abbrev integralHomology (X : Type) [TopologicalSpace X] (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- One singular simplex tracing the positively parametrized circle once. -/
def circleLoopSimplex : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).symm
    ⟨fun z : StdSimplex ℝ (Fin 2) => Circle.exp (2 * Real.pi * z.weights 1),
      Circle.exp.continuous.comp
        (continuous_const.mul (StdSimplex.continuous_weights_apply ℝ 1))⟩

def circleLoopChain : ModuleCat.of ℤ ℤ ⟶ (integralChains Circle).X 1 :=
  (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex circleLoopSimplex

theorem circleLoopChain_boundary : circleLoopChain ≫ (integralChains Circle).d 1 0 = 0 := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.circleLoopChain_boundary)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete circleLoopChain_boundary\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))















def circleFundamentalClass : integralHomology Circle 1 :=
  (((integralChains Circle).liftCycles circleLoopChain 0 (by simp) circleLoopChain_boundary) ≫
    (integralChains Circle).homologyπ 1) 1

theorem circleFundamentalClass_generates :
    ∀ x : integralHomology Circle 1, ∃! k : ℤ, k • circleFundamentalClass = x := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.circleFundamentalClass_generates)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete circleFundamentalClass_generates\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))


def curveClass {X : Type} [TopologicalSpace X] (c : C(Circle, X)) :
    integralHomology X 1 :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom c)) circleFundamentalClass

theorem curveClass_homotopy {X : Type} [TopologicalSpace X] (c d : C(Circle, X))
    (h : ContinuousMap.Homotopic c d) : curveClass c = curveClass d := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.curveClass_homotopy)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete curveClass_homotopy\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))








def componentKnot {n : ℕ} (L : OrientedLink n) (i : Fin n) : OrientedKnot where
  nonempty := Nat.zero_lt_one
  component _ := L.component i
  smoothEmbedding _ := L.smoothEmbedding i
  disjoint := fun _ _ h => (h (Subsingleton.elim _ _)).elim

abbrev knotComplement (K : OrientedKnot) := ↥(Set.range (K.component 0))ᶜ

def circleVector (z : Circle) : Euc 2 :=
  EuclideanSpace.single 0 (z : ℂ).re + EuclideanSpace.single 1 (z : ℂ).im
run_cmd do Lean.Elab.Command.elabCommand (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `command "run_cmd do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Elab.Command.liftCoreM <| Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  if let some (.thmInfo v) := data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.circleVector._proof_1) then\n    Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl v)\n"))
theorem circleVector_norm (z : Circle) : ‖circleVector z‖ = 1 := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.circleVector_norm)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete circleVector_norm\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))






theorem circleVector_mem_disk (z : Circle) : circleVector z ∈ tubeDiskOpen := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.circleVector_mem_disk)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete circleVector_mem_disk\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))






def tubeEuclideanExtension {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) (q : ℝ × Euc 2) : Euc 4 :=
  if h : q.2 ∈ tubeDiskOpen then
    (T.tube i (Circle.exp q.1, ⟨q.2, h⟩) : Euc 4)
  else (L.component i (Circle.exp q.1) : Euc 4)

/-- Outward-first orientation of the standard S³, followed by the positive
knot tangent and its ordered normal-disk frame. This fixes the sign of the
meridian calibration, rather than letting an arbitrary tube reverse it. -/
def PositiveTubeFraming {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L) : Prop :=
  ∀ i, 0 < Matrix.det (fun r c : Fin 4 =>
    (![ (L.component i 1 : Euc 4),
        fderiv ℝ (tubeEuclideanExtension T i) (0, 0) (1, 0),
        fderiv ℝ (tubeEuclideanExtension T i) (0, 0) (0, EuclideanSpace.single 0 1),
        fderiv ℝ (tubeEuclideanExtension T i) (0, 0) (0, EuclideanSpace.single 1 1)] r) c)

theorem tube_meridian_misses_core {K : OrientedKnot} (T : TubularNeighborhood K)
    (z : Circle) :
    T.tube 0 (1, ⟨circleVector z, circleVector_mem_disk z⟩) ∉
      Set.range (K.component 0) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.tube_meridian_misses_core)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete tube_meridian_misses_core\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))








def tubeMeridianPoint {K : OrientedKnot} (T : TubularNeighborhood K)
    (z : Circle) : knotComplement K :=
  ⟨T.tube 0 (1, ⟨circleVector z, circleVector_mem_disk z⟩),
    tube_meridian_misses_core T z⟩

theorem tubeMeridian_continuous {K : OrientedKnot} (T : TubularNeighborhood K) :
    Continuous (tubeMeridianPoint T) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.tubeMeridian_continuous)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete tubeMeridian_continuous\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))















def tubeMeridian {K : OrientedKnot} (T : TubularNeighborhood K) :
    C(Circle, knotComplement K) := ⟨tubeMeridianPoint T, tubeMeridian_continuous T⟩

variable {n : ℕ} (L : OrientedLink n)

theorem other_component_misses_core (i j : Fin n) (h : i ≠ j) (z : Circle) :
    L.component i z ∉ Set.range ((componentKnot L j).component 0) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.other_component_misses_core)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete other_component_misses_core\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))


def otherComponentPoint (i j : Fin n) (h : i ≠ j) (z : Circle) :
    knotComplement (componentKnot L j) :=
  ⟨L.component i z, other_component_misses_core L i j h z⟩

theorem otherComponent_continuous (i j : Fin n) (h : i ≠ j) :
    Continuous (otherComponentPoint L i j h) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.otherComponent_continuous)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete otherComponent_continuous\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))


def otherComponent (i j : Fin n) (h : i ≠ j) :
    C(Circle, knotComplement (componentKnot L j)) :=
  ⟨otherComponentPoint L i j h, otherComponent_continuous L i j h⟩

variable {T : TubularNeighborhood L} (E : SmoothExterior T)

theorem exterior_misses_core (j : Fin n) (x : E.Carrier) :
    E.toSphere x ∉ Set.range ((componentKnot L j).component 0) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.exterior_misses_core)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete exterior_misses_core\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))









def exteriorToKnotComplement (j : Fin n) (x : E.Carrier) :
    knotComplement (componentKnot L j) := ⟨E.toSphere x, exterior_misses_core L E j x⟩

theorem exteriorToKnotComplement_continuous (j : Fin n) :
    Continuous (exteriorToKnotComplement L E j) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.exteriorToKnotComplement_continuous)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete exteriorToKnotComplement_continuous\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))



def boundaryInComplement (F : LinkSpanningSurface.{0} E) (i j : Fin n) :
    C(Circle, knotComplement (componentKnot L j)) :=
  (⟨exteriorToKnotComplement L E j, exteriorToKnotComplement_continuous L E j⟩ :
    C(E.Carrier, knotComplement (componentKnot L j))).comp
    (F.embedding.continuousMap.comp
      ⟨(F.boundaryCircle i).toFun, (F.boundaryCircle i).smoothEmbedding.isEmbedding.continuous⟩)

theorem boundary_other_component_homology (F : LinkSpanningSurface.{0} E)
    (i j : Fin n) (h : i ≠ j) :
    curveClass (boundaryInComplement L E F i j) = curveClass (otherComponent L i j h) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.boundary_other_component_homology)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete boundary_other_component_homology\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))











































def boundaryComponent (F : LinkSpanningSurface.{0} E) (i : Fin n) :
    ConnectedComponents F.surface := ConnectedComponents.mk ((F.boundaryCircle i).toFun 1)

theorem boundaryCircle_in_component (F : LinkSpanningSurface.{0} E) (i : Fin n) (z : Circle) :
    ConnectedComponents.mk ((F.boundaryCircle i).toFun z) = boundaryComponent L E F i := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.boundaryCircle_in_component)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete boundaryCircle_in_component\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))







theorem boundaryComponent_surjective (F : LinkSpanningSurface.{0} E) :
    Function.Surjective (boundaryComponent L E F) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.boundaryComponent_surjective)).get!\n  let proof := (ci.value? (allowOpaque := true)).get!\n  let goal ← Lean.Elab.Tactic.getMainGoal\n  let ctx ← Lean.getLCtx\n  let mut type := ci.type\n  let mut args : Array Lean.Expr := #[]\n  while let .forallE binder _ body _ := type do\n    if let some localDecl := ctx.findFromUserName? binder then\n      args := args.push localDecl.toExpr\n      type := body.instantiate1 localDecl.toExpr\n    else\n      break\n  let mut term := proof\n  for arg in args do\n    if let .lam _ _ body _ := term then term := body.instantiate1 arg\n    else term := Lean.mkApp term arg\n  unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError \"pinned binder match incomplete boundaryComponent_surjective\"\n  Lean.Meta.checkWithKernel term\n  (← Lean.Elab.Tactic.getMainGoal).assign term\n"))










run_cmd do Lean.Elab.Command.elabCommand (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `command "run_cmd do\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let (data,_) ← Lean.Elab.Command.liftCoreM <| Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD \".\" / \"ProofData\" / \"prior_paid_linking.olean\")\n  let mut pending : Array Lean.ConstantInfo := #[]\n  for ci in data.constants do\n    if ((← Lean.Elab.Command.liftCoreM Lean.getEnv).setExporting false).find? ci.name |>.isNone then\n      pending := pending.push ci\n  while !pending.isEmpty do\n    let mut rest : Array Lean.ConstantInfo := #[]\n    for ci in pending do\n      let env := (← Lean.Elab.Command.liftCoreM Lean.getEnv).setExporting false\n      let value := (ci.value? (allowOpaque := true)).get!\n      let deps := ci.type.getUsedConstantsAsSet.merge value.getUsedConstantsAsSet\n      if deps.toArray.any (fun n => n != ci.name && (env.find? n).isNone) then\n        rest := rest.push ci\n      else\n        match ci with\n        | .defnInfo v => Lean.Elab.Command.liftCoreM <| Lean.addDecl (.defnDecl v)\n        | .thmInfo v => Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl v)\n        | _ => throwError \"unsupported baseline missing declaration\"\n    if rest.size == pending.size then throwError \"baseline missing declarations stuck\"\n    pending := rest\n"))

structure MeridianHomologyCoordinate (K : OrientedKnot) where
  tube : TubularNeighborhood K
  positive : PositiveTubeFraming tube
  coordinate : integralHomology (knotComplement K) 1 ≃ₗ[ℤ] ℤ
  meridian_positive : coordinate (curveClass (tubeMeridian tube)) = 1

variable {n : ℕ} (L : OrientedLink n)

abbrev LinkCoordinates := ∀ i : Fin n, MeridianHomologyCoordinate (componentKnot L i)


variable {T : TubularNeighborhood L} (E : SmoothExterior T)

def exteriorLinkingCoordinates (Q : LinkCoordinates L) :
    integralHomology E.Carrier 1 →ₗ[ℤ] (Fin n → ℤ) :=
  LinearMap.pi (fun j => (Q j).coordinate.toLinearMap.comp
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom
        (⟨exteriorToKnotComplement L E j, exteriorToKnotComplement_continuous L E j⟩ :
          C(E.Carrier, knotComplement (componentKnot L j))))).hom))

end
end SeifertSurfaces.GenusLinking

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Set Topology
open SeifertSurfaces.Foundations
open SeifertSurfaces.GenusLinking
open CurveComplexGenusTwo.CWHurewicz
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev HF (k : ℕ) :=
  (singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)

private def originalIntegralComparison (X : Type) [TopologicalSpace X] (k : ℕ) :
    H X k ≅ DifferentialGeometry.Topology.integralSingularHomology k X :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).mapIso
    ((ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm.toModuleIso)).app (TopCat.of X)

private theorem sphere_h1_zero {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (hd : 2 < Module.finrank ℝ V) : IsZero (H (Metric.sphere (0 : V) 1) 1) := by
  let v := DifferentialGeometry.Topology.unitSpherePointOfFinrankPos (E := V) (by omega)
  letI := DifferentialGeometry.Topology.unitSphere_pathConnected_of_finrank (E := V) (by omega)
  let W := (ℝ ∙ ((-v : Metric.sphere (0 : V) 1) : V))ᗮ
  have hdW : 1 < Module.finrank ℝ W := by
    have hw := DifferentialGeometry.Topology.unitSpherePoleHyperplane_finrank
      (E := V) (Module.finrank ℝ V - 1) (by omega) (-v)
    change Module.finrank ℝ W = Module.finrank ℝ V - 1 at hw
    omega
  letI := DifferentialGeometry.Topology.unitSphere_pathConnected_of_finrank (E := W) hdW
  let e := DifferentialGeometry.Topology.integralSphereHomologyOneReducedEquiv v
  letI : Subsingleton (DifferentialGeometry.Topology.integralReducedHomologyZero
      (Metric.sphere (0 : W) 1)) := DifferentialGeometry.Topology.integralReducedZero_subsingleton
  letI : Subsingleton (DifferentialGeometry.Topology.integralSingularHomology 1
      (Metric.sphere (0 : V) 1)) := e.injective.subsingleton
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (originalIntegralComparison _ 1)

private theorem threeSphere_h1_zero : IsZero (H ThreeSphere 1) :=
  sphere_h1_zero (by simp [Euc])

private theorem threeSphere_h2_zero : IsZero (H ThreeSphere 2) := by
  let v := DifferentialGeometry.Topology.unitSpherePointOfFinrankPos (E := Euc 4) (by simp [Euc])
  let W := (ℝ ∙ ((-v : ThreeSphere) : Euc 4))ᗮ
  have hdW : Module.finrank ℝ W = 3 :=
    DifferentialGeometry.Topology.unitSpherePoleHyperplane_finrank (E := Euc 4) 3 (by simp [Euc]) (-v)
  let e := DifferentialGeometry.Topology.integralSphereHomologyShiftEquiv 0 v
  have hw : IsZero (DifferentialGeometry.Topology.integralSingularHomology 1
      (Metric.sphere (0 : W) 1)) :=
    (sphere_h1_zero (V := W) (by omega)).of_iso (originalIntegralComparison _ 1).symm
  exact (hw.of_iso e.toModuleIso).of_iso (originalIntegralComparison ThreeSphere 2)

private theorem mv_intersection_bijective (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
    (hz1 : IsZero (H X 1)) (hz2 : IsZero (H X 2)) :
    Function.Bijective (actualMVDifference X U V 1) := by
  letI := ModuleCat.subsingleton_of_isZero hz1
  letI := ModuleCat.subsingleton_of_isZero hz2
  have hi := (ShortComplex.moduleCat_exact_iff _).mp
    (actualMV_exact_intersection X U V hU hV hc 1)
  have hs := (ShortComplex.moduleCat_exact_iff _).mp
    (actualMV_exact_pair X U V hU hV hc 1)
  constructor
  · apply (injective_iff_map_eq_zero (actualMVDifference X U V 1).hom).mpr
    intro a ha
    obtain ⟨b, hb⟩ := hi a ha
    have hb0 : b = 0 := Subsingleton.elim _ _
    simpa only [hb0, map_zero] using hb.symm
  · intro a
    exact hs a (Subsingleton.elim _ _)


private def coreComplement {n : ℕ} (L : OrientedLink n) (s : Finset (Fin n)) : Set ThreeSphere :=
  {x | ∀ i ∈ s, x ∉ Set.range (L.component i)}

private def coreComplementMap {n : ℕ} (L : OrientedLink n) (s : Finset (Fin n))
    (i : Fin n) (hi : i ∈ s) : C(coreComplement L s, knotComplement (componentKnot L i)) :=
  ⟨fun x => ⟨x.val, x.property i hi⟩, continuous_subtype_val.subtype_mk _⟩

private theorem coreComplement_open {n : ℕ} (L : OrientedLink n) (s : Finset (Fin n)) :
    IsOpen (coreComplement L s) := by
  have he : coreComplement L s = ⋂ i ∈ s, (Set.range (L.component i))ᶜ := by
    ext x
    simp [coreComplement]
  rw [he]
  exact isOpen_biInter_finset fun i hi =>
    (isCompact_range (L.smoothEmbedding i).isEmbedding.continuous).isClosed.isOpen_compl

private theorem coreComplement_insert {n : ℕ} (L : OrientedLink n) (s : Finset (Fin n)) (i : Fin n) :
    coreComplement L (insert i s) = coreComplement L s ∩ (Set.range (L.component i))ᶜ := by
  ext x
  simp [coreComplement, and_comm]


private def hmap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : H X 1 →ₗ[ℤ] H Y 1 := ((HF 1).map (TopCat.ofHom f)).hom

private theorem hmap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (x : H X 1) :
    hmap (g.comp f) x = hmap g (hmap f x) := by
  change ((HF 1).map (TopCat.ofHom (g.comp f))) x = _
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g from rfl,
    Functor.map_comp]
  rfl

private theorem hmap_homeomorph_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : Function.Injective (hmap (⟨e, e.continuous⟩ : C(X, Y))) := by
  intro a b hab
  have h := congrArg (hmap (⟨e.symm, e.symm.continuous⟩ : C(Y, X))) hab
  rw [← hmap_comp, ← hmap_comp] at h
  have hc : (⟨e.symm, e.symm.continuous⟩ : C(Y, X)).comp (⟨e, e.continuous⟩ : C(X, Y)) =
      ContinuousMap.id X := by ext x; exact e.symm_apply_apply x
  rw [hc] at h
  simpa [hmap, HF, TopCat.ofHom_id, Functor.map_id] using h

private theorem coreComplement_detects {n : ℕ} (L : OrientedLink n) (s : Finset (Fin n))
    (x : H (coreComplement L s) 1)
    (hx : ∀ i (hi : i ∈ s), hmap (coreComplementMap L s i hi) x = 0) : x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have he : coreComplement L ∅ = univ := by ext y; simp [coreComplement]
      let e := (Homeomorph.setCongr he).trans (Homeomorph.Set.univ ThreeSphere)
      letI : Subsingleton (H (coreComplement L ∅) 1) :=
        ModuleCat.subsingleton_of_isZero (threeSphere_h1_zero.of_iso
          ((HF 1).mapIso (TopCat.isoOfHomeo e)))
      exact Subsingleton.elim _ _
  | @insert i s hi ih =>
      let U := coreComplement L s
      let V := (Set.range (L.component i))ᶜ
      let e : coreComplement L (insert i s) ≃ₜ ↥(U ∩ V) :=
        Homeomorph.setCongr (coreComplement_insert L s i)
      let a : C(coreComplement L (insert i s), U) :=
        ⟨fun y => ⟨y.val, fun j hj => y.property j (Finset.mem_insert_of_mem hj)⟩,
          continuous_subtype_val.subtype_mk _⟩
      have ha : hmap a x = 0 := by
        apply ih
        intro j hj
        have heq : (coreComplementMap L s j hj).comp a =
            coreComplementMap L (insert i s) j (Finset.mem_insert_of_mem hj) := by
          ext y
          rfl
        rw [← hmap_comp, heq]
        exact hx j _
      have hcover : U ∪ V = univ := by
        apply Set.eq_univ_of_forall
        intro y
        by_cases hy : y ∈ V
        · exact Or.inr hy
        · apply Or.inl
          intro j hj hyj
          have hneq : j ≠ i := fun h => hi (h ▸ hj)
          have hyi : y ∈ Set.range (L.component i) := Classical.not_not.mp hy
          exact Set.disjoint_left.mp (L.disjoint hneq) hyj hyi
      have hU : IsOpen U := coreComplement_open L s
      have hV : IsOpen V :=
        (isCompact_range (L.smoothEmbedding i).isEmbedding.continuous).isClosed.isOpen_compl
      let q := hmap (⟨e, e.continuous⟩ : C(coreComplement L (insert i s), ↥(U ∩ V))) x
      have hq : actualMVDifference (TopCat.of ThreeSphere) U V 1 q = 0 := by
        rw [actualMVDifference_apply]
        apply Prod.ext
        · change hmap (⟨fun y : ↥(U ∩ V) => ⟨y.val, y.property.1⟩,
            continuous_subtype_val.subtype_mk _⟩ : C(↥(U ∩ V), U))
              (hmap (⟨e, e.continuous⟩ : C(coreComplement L (insert i s), ↥(U ∩ V))) x) = 0
          rw [← hmap_comp]
          exact ha
        · change -hmap (⟨fun y : ↥(U ∩ V) => ⟨y.val, y.property.2⟩,
            continuous_subtype_val.subtype_mk _⟩ : C(↥(U ∩ V), V))
              (hmap (⟨e, e.continuous⟩ : C(coreComplement L (insert i s), ↥(U ∩ V))) x) = 0
          rw [← hmap_comp]
          change -(hmap (coreComplementMap L (insert i s) i (Finset.mem_insert_self i s))) x = 0
          exact (congrArg Neg.neg (hx i _)).trans neg_zero

      have hq0 : q = 0 :=
        (injective_iff_map_eq_zero (actualMVDifference (TopCat.of ThreeSphere) U V 1).hom).mp
          (mv_intersection_bijective (TopCat.of ThreeSphere) U V hU hV hcover threeSphere_h1_zero threeSphere_h2_zero).1
          q hq
      have hinj : Function.Injective (hmap (⟨e, e.continuous⟩ : C(coreComplement L (insert i s), ↥(U ∩ V)))) :=
        hmap_homeomorph_injective e
      exact (injective_iff_map_eq_zero _).mp hinj x hq0


private noncomputable def tubeInv {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) (x : ThreeSphere) : TubeDomain :=
  if h : ∃ p, T.tube i p = x then Classical.choose h
  else (1, ⟨0, Metric.mem_ball_self zero_lt_two⟩)

private theorem tubeInv_right {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) (x : ThreeSphere) (hx : x ∈ Set.range (T.tube i)) :
    T.tube i (tubeInv T i x) = x := by
  classical
  classical
  by_cases h : ∃ p, T.tube i p = x
  · simp only [tubeInv, dite_eq_left h]
    exact Classical.choose_spec h
  · simp only [tubeInv, dite_eq_right h]
    exact False.elim (h hx)

private theorem tubeInv_left {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) (p : TubeDomain) : tubeInv T i (T.tube i p) = p := by
  apply (T.smoothEmbedding i).isEmbedding.injective
  exact tubeInv_right T i _ ⟨p, rfl⟩

private theorem tubeInv_continuousAt {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) (x : ThreeSphere) (hx : x ∈ Set.range (T.tube i)) :
    ContinuousAt (tubeInv T i) x := by
  have heq : T.tube i ∘ tubeInv T i =ᶠ[nhds x] id := by
    filter_upwards [(T.image_open i).mem_nhds hx] with y hy
    exact tubeInv_right T i y hy
  apply (T.smoothEmbedding i).isEmbedding.isInducing.continuousAt_iff.mpr
  exact continuousAt_id.congr_of_eventuallyEq heq

private def radialPush (v : Euc 2) : Euc 2 := (max 1 ‖v‖ / ‖v‖) • v

private theorem radialPush_norm {v : Euc 2} (hv : v ≠ 0) :
    ‖radialPush v‖ = max 1 ‖v‖ := by
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [radialPush, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_mul_cancel₀ _ (ne_of_gt hr)]

private theorem radialPush_eq {v : Euc 2} (hv : 1 ≤ ‖v‖) : radialPush v = v := by
  have hr : ‖v‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hv)
  simp [radialPush, max_eq_right hv, hr]

private theorem radialPush_continuousAt {v : Euc 2} (hv : v ≠ 0) :
    ContinuousAt radialPush v := by
  exact ((continuous_const.max continuous_norm).continuousAt.div continuous_norm.continuousAt
    (norm_ne_zero_iff.mpr hv)).smul continuousAt_id

private theorem radialPush_mem {v : TubeDisk} (hv : (v : Euc 2) ≠ 0) :
    radialPush v ∈ tubeDiskOpen := by
  change ‖radialPush v - 0‖ < 2
  rw [sub_zero, radialPush_norm hv]
  apply max_lt
  · norm_num
  · change ‖(v : Euc 2)‖ < 2
    have h : ‖(v : Euc 2) - 0‖ < 2 := v.property
    simpa only [sub_zero] using h

private theorem tubeInv_normal_ne_zero {n : ℕ} (L : OrientedLink n) (T : TubularNeighborhood L)
    (i : Fin n) (x : coreComplement L Finset.univ)
    (hx : (x : ThreeSphere) ∈ Set.range (T.tube i)) :
    ((tubeInv T i x).2 : Euc 2) ≠ 0 := by
  intro hv
  apply x.property i (Finset.mem_univ i)
  refine ⟨(tubeInv T i x).1, ?_⟩
  rw [← T.core i (tubeInv T i x).1]
  have hp : ((tubeInv T i x).1, (⟨0, Metric.mem_ball_self zero_lt_two⟩ : TubeDisk)) =
      tubeInv T i x := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext hv.symm
  rw [hp]
  exact tubeInv_right T i _ hx


private theorem radialPush_mem_all (v : TubeDisk) : radialPush v ∈ tubeDiskOpen := by
  by_cases hv : (v : Euc 2) = 0
  · simp [radialPush, hv, tubeDiskOpen]
  · exact radialPush_mem hv

private def tubePushed {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) (x : ThreeSphere) : ThreeSphere :=
  T.tube i ((tubeInv T i x).1, ⟨radialPush (tubeInv T i x).2, radialPush_mem_all _⟩)

private def rawRetraction {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (x : ThreeSphere) : ThreeSphere :=
  if h : ∃ i, x ∈ Set.range (T.tube i) then tubePushed T (Classical.choose h) x else x

private theorem rawRetraction_on_tube {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) (x : ThreeSphere) (hx : x ∈ Set.range (T.tube i)) :
    rawRetraction T x = tubePushed T i x := by
  classical
  have h : ∃ j, x ∈ Set.range (T.tube j) := ⟨i, hx⟩
  have heq : Classical.choose h = i := by
    by_contra hne
    exact Set.disjoint_left.mp (T.disjoint hne) (Classical.choose_spec h) hx
  simp only [rawRetraction, dite_eq_left h, heq]

private theorem tubePushed_continuousAt {n : ℕ} (L : OrientedLink n) (T : TubularNeighborhood L)
    (i : Fin n) (x : coreComplement L Finset.univ)
    (hx : (x : ThreeSphere) ∈ Set.range (T.tube i)) :
    ContinuousAt (tubePushed T i) (x : ThreeSphere) := by
  have hi := tubeInv_continuousAt T i x hx
  have hn : ContinuousAt radialPush ((tubeInv T i x).2 : Euc 2) :=
    radialPush_continuousAt (tubeInv_normal_ne_zero L T i x hx)
  have hiN : ContinuousAt (fun y : ThreeSphere => ((tubeInv T i y).2 : Euc 2)) x :=
    (continuous_subtype_val : Continuous (Subtype.val : TubeDisk → Euc 2)).continuousAt.comp
      (continuous_snd.continuousAt.comp hi)
  have hr : ContinuousAt (fun y : ThreeSphere => radialPush (tubeInv T i y).2) x :=
    ContinuousAt.comp (f := fun y : ThreeSphere => ((tubeInv T i y).2 : Euc 2))
      (g := radialPush) hn hiN
  have hp : ContinuousAt (fun y : ThreeSphere =>
      ((tubeInv T i y).1, (⟨radialPush (tubeInv T i y).2, radialPush_mem_all _⟩ : TubeDisk))) x :=
    (continuous_fst.continuousAt.comp hi).prodMk (hr.codRestrict (fun y => radialPush_mem_all (tubeInv T i y).2))
  exact (T.smoothEmbedding i).isEmbedding.continuous.continuousAt.comp hp

private def closedTube {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) : Set ThreeSphere :=
  T.tube i '' (Set.ofPred (fun p : TubeDomain => ‖(p.2 : Euc 2)‖ ≤ 1))

private abbrev ClosedNormalDisk := ↥(Metric.closedBall (0 : Euc 2) (1 : ℝ))

private def closedNormalDiskLift : C(ClosedNormalDisk, TubeDisk) :=
  ⟨fun v => ⟨v.val, by
    have h : ‖(v : Euc 2) - 0‖ ≤ 1 := v.property
    change ‖(v : Euc 2) - 0‖ < 2
    linarith⟩, by
      apply continuous_induced_rng.mpr
      exact continuous_subtype_val⟩

private def closedTubeMap {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) : C(Circle × ClosedNormalDisk, ThreeSphere) :=
  ⟨fun p => T.tube i (p.1, closedNormalDiskLift p.2),
    (T.smoothEmbedding i).isEmbedding.continuous.comp
      (continuous_fst.prodMk (closedNormalDiskLift.continuous.comp continuous_snd))⟩

private theorem closedTube_isClosed {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) : IsClosed (closedTube T i) := by
  let liftDisk := closedNormalDiskLift
  let f := closedTubeMap T i
  have he : Set.range f = closedTube T i := by
    ext y
    constructor
    · rintro ⟨⟨z, v⟩, rfl⟩
      refine ⟨(z, liftDisk v), ?_, rfl⟩
      change ‖(v : Euc 2)‖ ≤ 1
      have h : ‖(v : Euc 2) - 0‖ ≤ 1 := v.property
      simpa only [sub_zero] using h
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(p.1, ⟨(p.2 : Euc 2), ?_⟩), ?_⟩
      · change ‖(p.2 : Euc 2)‖ ≤ 1 at hp
        simpa [Metric.mem_closedBall, dist_zero_right] using hp
      · rfl
  rw [← he]
  exact (isCompact_range f.continuous).isClosed

private theorem tubePushed_eq_of_off_closed {n : ℕ} {L : OrientedLink n}
    (T : TubularNeighborhood L) (i : Fin n) (x : ThreeSphere)
    (hx : x ∈ Set.range (T.tube i)) (hc : x ∉ closedTube T i) : tubePushed T i x = x := by
  have hn : 1 ≤ ‖((tubeInv T i x).2 : Euc 2)‖ := by
    by_contra h
    exact hc ⟨tubeInv T i x, le_of_lt (lt_of_not_ge h), tubeInv_right T i x hx⟩
  have heq : ((tubeInv T i x).1,
      (⟨radialPush (tubeInv T i x).2, radialPush_mem_all _⟩ : TubeDisk)) = tubeInv T i x :=
    Prod.ext rfl (Subtype.ext (radialPush_eq hn))
  exact (congrArg (T.tube i) heq).trans (tubeInv_right T i x hx)

private theorem rawRetraction_eq_of_off_closed {n : ℕ} {L : OrientedLink n}
    (T : TubularNeighborhood L) (x : ThreeSphere)
    (hx : x ∉ ⋃ i, closedTube T i) : rawRetraction T x = x := by
  classical
  by_cases h : ∃ i, x ∈ Set.range (T.tube i)
  · rw [rawRetraction, dite_eq_left h]
    exact tubePushed_eq_of_off_closed T _ x (Classical.choose_spec h)
      (fun hc => hx (Set.mem_iUnion.mpr ⟨_, hc⟩))
  · simp only [rawRetraction, dite_eq_right h]

private theorem rawRetraction_continuous {n : ℕ} (L : OrientedLink n) (T : TubularNeighborhood L) :
    Continuous (fun x : coreComplement L Finset.univ => rawRetraction T x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases h : ∃ i, (x : ThreeSphere) ∈ Set.range (T.tube i)
  · obtain ⟨i, hi⟩ := h
    have heq : (fun y : coreComplement L Finset.univ => rawRetraction T y) =ᶠ[nhds x]
        (fun y => tubePushed T i y) := by
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((T.image_open i).mem_nhds hi)] with y hy
      exact rawRetraction_on_tube T i y hy
    exact ((tubePushed_continuousAt L T i x hi).comp
      continuous_subtype_val.continuousAt).congr_of_eventuallyEq heq
  · have hc : (x : ThreeSphere) ∉ ⋃ i, closedTube T i := by
      intro hc
      obtain ⟨i, hix⟩ := Set.mem_iUnion.mp hc
      obtain ⟨p, hp, hpx⟩ := hix
      exact h ⟨i, p, hpx⟩
    have hopen : IsOpen (⋃ i, closedTube T i)ᶜ :=
      (isClosed_iUnion_of_finite (fun i => closedTube_isClosed T i)).isOpen_compl
    have heq : (fun y : coreComplement L Finset.univ => rawRetraction T y) =ᶠ[nhds x]
        (fun y => (y : ThreeSphere)) := by
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (hopen.mem_nhds hc)] with y hy
      exact rawRetraction_eq_of_off_closed T y hy
    exact continuous_subtype_val.continuousAt.congr_of_eventuallyEq heq


private theorem tubePushed_exterior {n : ℕ} (L : OrientedLink n) (T : TubularNeighborhood L)
    (i : Fin n) (x : coreComplement L Finset.univ)
    (hx : (x : ThreeSphere) ∈ Set.range (T.tube i)) : tubePushed T i x ∈ T.exteriorSet := by
  intro h
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
  obtain ⟨p, hp, heq⟩ := hj
  by_cases hji : j = i
  · subst j
    have he := (T.smoothEmbedding i).isEmbedding.injective heq
    have heN := congrArg (fun q : TubeDomain => (q.2 : Euc 2)) he
    change ‖(p.2 : Euc 2)‖ < 1 at hp
    rw [heN, radialPush_norm (tubeInv_normal_ne_zero L T i x hx)] at hp
    exact (not_lt_of_ge (le_max_left 1 _)) hp
  · exact Set.disjoint_left.mp (T.disjoint hji) ⟨p, heq⟩
      ⟨((tubeInv T i x).1, ⟨radialPush (tubeInv T i x).2, radialPush_mem_all _⟩), rfl⟩

private theorem rawRetraction_exterior {n : ℕ} (L : OrientedLink n) (T : TubularNeighborhood L)
    (x : coreComplement L Finset.univ) : rawRetraction T x ∈ T.exteriorSet := by
  classical
  by_cases h : ∃ i, (x : ThreeSphere) ∈ Set.range (T.tube i)
  · rw [rawRetraction, dite_eq_left h]
    exact tubePushed_exterior L T _ x (Classical.choose_spec h)
  · rw [rawRetraction, dite_eq_right h]
    intro hx
    obtain ⟨i, p, hp, hpx⟩ := Set.mem_iUnion.mp hx
    exact h ⟨i, p, hpx⟩

private def exteriorCoreMap {n : ℕ} (L : OrientedLink n) {T : TubularNeighborhood L}
    (E : SmoothExterior T) : C(E.Carrier, coreComplement L Finset.univ) :=
  ⟨fun x => ⟨E.toSphere x, fun i _hi => exterior_misses_core L E i x⟩,
    continuous_subtype_val.subtype_mk _⟩

private def exteriorRetraction {n : ℕ} (L : OrientedLink n) {T : TubularNeighborhood L}
    (E : SmoothExterior T) : C(coreComplement L Finset.univ, E.Carrier) :=
  ⟨fun x => ⟨rawRetraction T x, rawRetraction_exterior L T x⟩,
    (rawRetraction_continuous L T).subtype_mk _⟩

private theorem rawRetraction_fix_exterior {n : ℕ} (L : OrientedLink n)
    {T : TubularNeighborhood L} (E : SmoothExterior T) (x : E.Carrier) :
    rawRetraction T (E.toSphere x) = E.toSphere x := by
  classical
  by_cases h : ∃ i, E.toSphere x ∈ Set.range (T.tube i)
  · obtain ⟨i, hi⟩ := h
    rw [rawRetraction_on_tube T i _ hi]
    have hn : 1 ≤ ‖((tubeInv T i (E.toSphere x)).2 : Euc 2)‖ := by
      by_contra hn
      apply x.property
      exact Set.mem_iUnion.mpr ⟨i, tubeInv T i (E.toSphere x), lt_of_not_ge hn,
        tubeInv_right T i _ hi⟩
    have heq : ((tubeInv T i (E.toSphere x)).1,
        (⟨radialPush (tubeInv T i (E.toSphere x)).2, radialPush_mem_all _⟩ : TubeDisk)) =
        tubeInv T i (E.toSphere x) :=
      Prod.ext rfl (Subtype.ext (radialPush_eq hn))
    exact (congrArg (T.tube i) heq).trans (tubeInv_right T i _ hi)
  · simp only [rawRetraction, dite_eq_right h]

private theorem exteriorRetraction_left {n : ℕ} (L : OrientedLink n)
    {T : TubularNeighborhood L} (E : SmoothExterior T) :
    (exteriorRetraction L E).comp (exteriorCoreMap L E) = ContinuousMap.id E.Carrier := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact rawRetraction_fix_exterior L E x

private theorem exterior_h1_detects {n : ℕ} (L : OrientedLink n)
    {T : TubularNeighborhood L} (E : SmoothExterior T) (x : integralHomology E.Carrier 1)
    (hx : ∀ i, hmap (⟨exteriorToKnotComplement L E i,
      exteriorToKnotComplement_continuous L E i⟩ : C(E.Carrier, knotComplement (componentKnot L i))) x = 0) :
    x = 0 := by
  have hinc : hmap (exteriorCoreMap L E) x = 0 := by
    apply coreComplement_detects
    intro i hi
    rw [← hmap_comp]
    exact hx i
  have hr := congrArg (hmap (exteriorRetraction L E)) hinc
  rw [map_zero, ← hmap_comp, exteriorRetraction_left] at hr
  simpa [hmap, HF, TopCat.ofHom_id, Functor.map_id] using hr


private theorem coreComplement_surjects {n : ℕ} (L : OrientedLink n) (s : Finset (Fin n))
    (v : ∀ i : Fin n, H (knotComplement (componentKnot L i)) 1) :
    ∃ x : H (coreComplement L s) 1,
      ∀ i (hi : i ∈ s), hmap (coreComplementMap L s i hi) x = v i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => (Finset.notMem_empty i hi).elim⟩
  | @insert i s hi ih =>
      obtain ⟨a, ha⟩ := ih
      let U := coreComplement L s
      let V := (Set.range (L.component i))ᶜ
      have hU : IsOpen U := coreComplement_open L s
      have hV : IsOpen V :=
        (isCompact_range (L.smoothEmbedding i).isEmbedding.continuous).isClosed.isOpen_compl
      have hc : U ∪ V = univ := by
        apply Set.eq_univ_of_forall
        intro y
        by_cases hy : y ∈ V
        · exact Or.inr hy
        · apply Or.inl
          intro j hj hyj
          have hneq : j ≠ i := fun h => hi (h ▸ hj)
          exact Set.disjoint_left.mp (L.disjoint hneq) hyj (Classical.not_not.mp hy)
      obtain ⟨q, hq⟩ := (mv_intersection_bijective (TopCat.of ThreeSphere)
        U V hU hV hc threeSphere_h1_zero threeSphere_h2_zero).2 (a, -v i)
      have hqU : actualSubsetHomologyMap (TopCat.of ThreeSphere)
          (U ∩ V) U Set.inter_subset_left 1 q = a := by
        have h := congrArg Prod.fst hq
        rw [actualMVDifference_apply] at h
        exact h
      have hqV : actualSubsetHomologyMap (TopCat.of ThreeSphere)
          (U ∩ V) V Set.inter_subset_right 1 q = v i := by
        have h := congrArg Prod.snd hq
        rw [actualMVDifference_apply] at h
        exact neg_injective h
      let e : coreComplement L (insert i s) ≃ₜ ↥(U ∩ V) :=
        Homeomorph.setCongr (coreComplement_insert L s i)
      let back : C(↥(U ∩ V), coreComplement L (insert i s)) := ⟨e.symm, e.symm.continuous⟩
      refine ⟨hmap back q, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [← hmap_comp]
        exact hqV
      · let aMap : C(↥(U ∩ V), U) :=
          ⟨fun y => ⟨y.val, y.property.1⟩, continuous_subtype_val.subtype_mk _⟩
        have heq : (coreComplementMap L (insert i s) j (Finset.mem_insert_of_mem hj)).comp back =
            (coreComplementMap L s j hj).comp aMap := by ext y; rfl
        rw [← hmap_comp, heq, hmap_comp]
        change hmap (coreComplementMap L s j hj)
          (actualSubsetHomologyMap (TopCat.of ThreeSphere) (U ∩ V) U Set.inter_subset_left 1 q) = v j
        rw [hqU]
        exact ha j hj

private def radialAt (t : unitInterval) (v : Euc 2) : Euc 2 :=
  (1 - (t : ℝ)) • v + (t : ℝ) • radialPush v

private theorem radialAt_mem (t : unitInterval) (v : TubeDisk) : radialAt t v ∈ tubeDiskOpen :=
  (convex_ball (0 : Euc 2) 2) v.property (radialPush_mem_all v)
    (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))

private theorem radialAt_eq (t : unitInterval) {v : Euc 2} (hv : 1 ≤ ‖v‖) : radialAt t v = v := by
  rw [radialAt, radialPush_eq hv, ← add_smul, sub_add_cancel, one_smul]

private theorem radialAt_ne_zero (t : unitInterval) {v : Euc 2} (hv : v ≠ 0) : radialAt t v ≠ 0 := by
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hmax : 0 < max 1 ‖v‖ / ‖v‖ := div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hr
  have he : radialAt t v = (1 - (t : ℝ) + (t : ℝ) * (max 1 ‖v‖ / ‖v‖)) • v := by
    simp only [radialAt, radialPush, smul_smul, add_smul]
  have hc : 0 < 1 - (t : ℝ) + (t : ℝ) * (max 1 ‖v‖ / ‖v‖) := by
    by_cases ht : (t : ℝ) = 0
    · simp [ht]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2) (mul_pos htpos hmax)
  rw [he]
  exact smul_ne_zero (ne_of_gt hc) hv

private def tubeAt {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) (p : unitInterval × ThreeSphere) : ThreeSphere :=
  T.tube i ((tubeInv T i p.2).1, ⟨radialAt p.1 (tubeInv T i p.2).2, radialAt_mem _ _⟩)

private def rawTubeHomotopy {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (p : unitInterval × ThreeSphere) : ThreeSphere :=
  if h : ∃ i, p.2 ∈ Set.range (T.tube i) then tubeAt T (Classical.choose h) p else p.2

private theorem rawTubeHomotopy_on_tube {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (i : Fin n) (p : unitInterval × ThreeSphere) (hx : p.2 ∈ Set.range (T.tube i)) :
    rawTubeHomotopy T p = tubeAt T i p := by
  classical
  have h : ∃ j, p.2 ∈ Set.range (T.tube j) := ⟨i, hx⟩
  have heq : Classical.choose h = i := by
    by_contra hne
    exact Set.disjoint_left.mp (T.disjoint hne) (Classical.choose_spec h) hx
  simp only [rawTubeHomotopy, dite_eq_left h, heq]

private theorem rawTubeHomotopy_off_closed {n : ℕ} {L : OrientedLink n}
    (T : TubularNeighborhood L) (p : unitInterval × ThreeSphere)
    (hx : p.2 ∉ ⋃ i, closedTube T i) : rawTubeHomotopy T p = p.2 := by
  classical
  by_cases h : ∃ i, p.2 ∈ Set.range (T.tube i)
  · rw [rawTubeHomotopy, dite_eq_left h]
    have hi : p.2 ∈ Set.range (T.tube (Classical.choose h)) := Classical.choose_spec h
    have hn : 1 ≤ ‖((tubeInv T (Classical.choose h) p.2).2 : Euc 2)‖ := by
      by_contra hn
      apply hx
      exact Set.mem_iUnion.mpr ⟨Classical.choose h, tubeInv T _ p.2,
        le_of_lt (lt_of_not_ge hn), tubeInv_right T _ _ hi⟩
    have heq : ((tubeInv T (Classical.choose h) p.2).1,
        (⟨radialAt p.1 (tubeInv T (Classical.choose h) p.2).2, radialAt_mem _ _⟩ : TubeDisk)) =
        tubeInv T (Classical.choose h) p.2 :=
      Prod.ext rfl (Subtype.ext (radialAt_eq p.1 hn))
    exact (congrArg (T.tube (Classical.choose h)) heq).trans (tubeInv_right T _ _ hi)
  · simp only [rawTubeHomotopy, dite_eq_right h]


private theorem tubeAt_continuousAt {n : ℕ} (L : OrientedLink n) (T : TubularNeighborhood L)
    (i : Fin n) (t : unitInterval) (x : coreComplement L Finset.univ)
    (hx : (x : ThreeSphere) ∈ Set.range (T.tube i)) :
    ContinuousAt (tubeAt T i) (t, (x : ThreeSphere)) := by
  have hi : ContinuousAt (fun p : unitInterval × ThreeSphere => tubeInv T i p.2) (t, (x : ThreeSphere)) :=
    ContinuousAt.comp (f := Prod.snd) (g := tubeInv T i)
      (tubeInv_continuousAt T i (x : ThreeSphere) hx) continuous_snd.continuousAt
  have hn : ContinuousAt (fun p : unitInterval × ThreeSphere => ((tubeInv T i p.2).2 : Euc 2))
      (t, (x : ThreeSphere)) :=
    (continuous_subtype_val : Continuous (Subtype.val : TubeDisk → Euc 2)).continuousAt.comp
      (continuous_snd.continuousAt.comp hi)
  have hp : ContinuousAt (fun p : unitInterval × ThreeSphere => radialPush (tubeInv T i p.2).2)
      (t, (x : ThreeSphere)) :=
    ContinuousAt.comp (f := fun p : unitInterval × ThreeSphere => ((tubeInv T i p.2).2 : Euc 2))
      (g := radialPush) (radialPush_continuousAt (tubeInv_normal_ne_zero L T i x hx)) hn
  have ht : Continuous (fun p : unitInterval × ThreeSphere => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hr : ContinuousAt (fun p : unitInterval × ThreeSphere => radialAt p.1 (tubeInv T i p.2).2)
      (t, (x : ThreeSphere)) :=
    (((continuous_const.sub ht).continuousAt).smul hn).add (ht.continuousAt.smul hp)
  have hcoord : ContinuousAt (fun p : unitInterval × ThreeSphere =>
      ((tubeInv T i p.2).1, (⟨radialAt p.1 (tubeInv T i p.2).2, radialAt_mem _ _⟩ : TubeDisk)))
      (t, (x : ThreeSphere)) :=
    (continuous_fst.continuousAt.comp hi).prodMk (hr.codRestrict (fun p => radialAt_mem _ _))
  exact (T.smoothEmbedding i).isEmbedding.continuous.continuousAt.comp hcoord

private theorem rawTubeHomotopy_continuous {n : ℕ} (L : OrientedLink n) (T : TubularNeighborhood L) :
    Continuous (fun p : unitInterval × coreComplement L Finset.univ =>
      rawTubeHomotopy T (p.1, (p.2 : ThreeSphere))) := by
  let c : C(unitInterval × coreComplement L Finset.univ, unitInterval × ThreeSphere) :=
    ⟨fun p => (p.1, (p.2 : ThreeSphere)),
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩
  rw [continuous_iff_continuousAt]
  intro p
  by_cases h : ∃ i, (p.2 : ThreeSphere) ∈ Set.range (T.tube i)
  · obtain ⟨i, hi⟩ := h
    have hopen : IsOpen (Set.ofPred (fun q : unitInterval × coreComplement L Finset.univ =>
        (q.2 : ThreeSphere) ∈ Set.range (T.tube i))) :=
      (T.image_open i).preimage (continuous_subtype_val.comp continuous_snd)
    have heq : (fun q : unitInterval × coreComplement L Finset.univ =>
        rawTubeHomotopy T (q.1, (q.2 : ThreeSphere))) =ᶠ[nhds p]
        (fun q => tubeAt T i (q.1, (q.2 : ThreeSphere))) := by
      filter_upwards [hopen.mem_nhds hi] with q hq
      exact rawTubeHomotopy_on_tube T i _ hq
    exact (ContinuousAt.comp (f := c) (g := tubeAt T i)
      (tubeAt_continuousAt L T i p.1 p.2 hi) c.continuous.continuousAt).congr_of_eventuallyEq heq
  · have hc : (p.2 : ThreeSphere) ∉ ⋃ i, closedTube T i := by
      intro hp
      obtain ⟨i, hix⟩ := Set.mem_iUnion.mp hp
      obtain ⟨q, hq, hqx⟩ := hix
      exact h ⟨i, q, hqx⟩
    have hopen : IsOpen (Set.ofPred (fun q : unitInterval × coreComplement L Finset.univ =>
        (q.2 : ThreeSphere) ∉ ⋃ i, closedTube T i)) :=
      ((isClosed_iUnion_of_finite (fun i => closedTube_isClosed T i)).isOpen_compl).preimage
        (continuous_subtype_val.comp continuous_snd)
    have heq : (fun q : unitInterval × coreComplement L Finset.univ =>
        rawTubeHomotopy T (q.1, (q.2 : ThreeSphere))) =ᶠ[nhds p]
        (fun q => (q.2 : ThreeSphere)) := by
      filter_upwards [hopen.mem_nhds hc] with q hq
      exact rawTubeHomotopy_off_closed T _ hq
    exact (continuous_subtype_val.comp continuous_snd).continuousAt.congr_of_eventuallyEq heq

private theorem rawTubeHomotopy_misses_cores {n : ℕ} (L : OrientedLink n) (T : TubularNeighborhood L)
    (t : unitInterval) (x : coreComplement L Finset.univ) :
    rawTubeHomotopy T (t, (x : ThreeSphere)) ∈ coreComplement L Finset.univ := by
  classical
  intro j _ hj
  by_cases h : ∃ i, (x : ThreeSphere) ∈ Set.range (T.tube i)
  · obtain ⟨i, hi⟩ := h
    rw [rawTubeHomotopy_on_tube T i _ hi] at hj
    obtain ⟨w, hw⟩ := hj
    by_cases hji : j = i
    · subst j
      rw [← T.core i w] at hw
      have he := (T.smoothEmbedding i).isEmbedding.injective hw
      have hv := congrArg (fun p : TubeDomain => (p.2 : Euc 2)) he
      exact (radialAt_ne_zero t (tubeInv_normal_ne_zero L T i x hi)) hv.symm
    · exact Set.disjoint_left.mp (T.disjoint hji)
        ⟨(w, ⟨0, Metric.mem_ball_self zero_lt_two⟩), (T.core j w).trans hw⟩
        ⟨((tubeInv T i x).1, ⟨radialAt t (tubeInv T i x).2, radialAt_mem _ _⟩), rfl⟩
  · rw [rawTubeHomotopy, dite_eq_right h] at hj
    exact x.property j (Finset.mem_univ j) hj

private theorem rawTubeHomotopy_zero {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (x : ThreeSphere) : rawTubeHomotopy T (0, x) = x := by
  classical
  by_cases h : ∃ i, x ∈ Set.range (T.tube i)
  · obtain ⟨i, hi⟩ := h
    rw [rawTubeHomotopy_on_tube T i _ hi]
    have heq : ((tubeInv T i x).1,
        (⟨radialAt 0 (tubeInv T i x).2, radialAt_mem _ _⟩ : TubeDisk)) = tubeInv T i x := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp [radialAt]
    exact (congrArg (T.tube i) heq).trans (tubeInv_right T i _ hi)
  · simp only [rawTubeHomotopy, dite_eq_right h]

private theorem rawTubeHomotopy_one {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)
    (x : ThreeSphere) : rawTubeHomotopy T (1, x) = rawRetraction T x := by
  classical
  by_cases h : ∃ i, x ∈ Set.range (T.tube i)
  · rw [rawTubeHomotopy, rawRetraction, dite_eq_left h, dite_eq_left h]
    apply congrArg (T.tube (Classical.choose h))
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [radialAt]
  · simp only [rawTubeHomotopy, rawRetraction, dite_eq_right h]

private def exteriorCoreHomotopy {n : ℕ} (L : OrientedLink n)
    {T : TubularNeighborhood L} (E : SmoothExterior T) :
    ContinuousMap.Homotopy (ContinuousMap.id (coreComplement L Finset.univ))
      ((exteriorCoreMap L E).comp (exteriorRetraction L E)) where
  toFun p := ⟨rawTubeHomotopy T (p.1, (p.2 : ThreeSphere)), rawTubeHomotopy_misses_cores L T p.1 p.2⟩
  continuous_toFun := (rawTubeHomotopy_continuous L T).subtype_mk _
  map_zero_left x := Subtype.ext (rawTubeHomotopy_zero T x)
  map_one_left x := Subtype.ext (rawTubeHomotopy_one T x)

private theorem exteriorCore_hmap_right {n : ℕ} (L : OrientedLink n)
    {T : TubularNeighborhood L} (E : SmoothExterior T) (x : H (coreComplement L Finset.univ) 1) :
    hmap (exteriorCoreMap L E) (hmap (exteriorRetraction L E) x) = x := by
  have he := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (C := ModuleCat.{0} ℤ) (X := TopCat.of (coreComplement L Finset.univ))
    (Y := TopCat.of (coreComplement L Finset.univ))
    (f := TopCat.ofHom (ContinuousMap.id _))
    (g := TopCat.ofHom ((exteriorCoreMap L E).comp (exteriorRetraction L E)))
    (exteriorCoreHomotopy L E) (ModuleCat.of ℤ ℤ) 1
  change (HF 1).map (TopCat.ofHom (ContinuousMap.id (coreComplement L Finset.univ))) =
    (HF 1).map (TopCat.ofHom ((exteriorCoreMap L E).comp (exteriorRetraction L E))) at he
  rw [show TopCat.ofHom (ContinuousMap.id (coreComplement L Finset.univ)) =
      𝟙 (TopCat.of (coreComplement L Finset.univ)) from rfl, (HF 1).map_id] at he
  rw [← hmap_comp]
  have heval := congrArg (fun f : H (coreComplement L Finset.univ) 1 ⟶
    H (coreComplement L Finset.univ) 1 => f x) he
  change x = hmap ((exteriorCoreMap L E).comp (exteriorRetraction L E)) x at heval
  simpa only [hmap, HF, TopCat.ofHom_id, Functor.map_id, ModuleCat.id_apply] using heval.symm


namespace SeifertSurfaces.GenusLinking
variable {n : ℕ} (L : OrientedLink n)
variable {T : TubularNeighborhood L} (E : SmoothExterior T)

theorem exteriorLinkingCoordinates_bijective (Q : LinkCoordinates L) :
    Function.Bijective (exteriorLinkingCoordinates L E Q) := by
  constructor
  · apply (injective_iff_map_eq_zero (exteriorLinkingCoordinates L E Q)).mpr
    intro x hx
    apply exterior_h1_detects L E x
    intro i
    have hi := congrFun hx i
    change (Q i).coordinate (hmap (⟨exteriorToKnotComplement L E i,
      exteriorToKnotComplement_continuous L E i⟩ : C(E.Carrier, knotComplement (componentKnot L i))) x) = 0 at hi
    exact (Q i).coordinate.injective (hi.trans (map_zero (Q i).coordinate).symm)
  · intro v
    obtain ⟨x, hx⟩ := coreComplement_surjects L Finset.univ (fun i => (Q i).coordinate.symm (v i))
    refine ⟨hmap (exteriorRetraction L E) x, ?_⟩
    ext i
    change (Q i).coordinate (hmap (⟨exteriorToKnotComplement L E i,
      exteriorToKnotComplement_continuous L E i⟩ : C(E.Carrier, knotComplement (componentKnot L i)))
        (hmap (exteriorRetraction L E) x)) = v i
    have heq : (⟨exteriorToKnotComplement L E i,
        exteriorToKnotComplement_continuous L E i⟩ : C(E.Carrier, knotComplement (componentKnot L i))) =
        (coreComplementMap L Finset.univ i (Finset.mem_univ i)).comp (exteriorCoreMap L E) := by
      ext y
      rfl
    rw [heq, hmap_comp, exteriorCore_hmap_right, hx i (Finset.mem_univ i)]
    exact (Q i).coordinate.apply_symm_apply (v i)

def totalLinking (Q : LinkCoordinates L) : integralHomology E.Carrier 1 →ₗ[ℤ] ℤ :=
  ∑ j : Fin n, LinearMap.proj j ∘ₗ exteriorLinkingCoordinates L E Q

theorem totalLinking_surjective (Q : LinkCoordinates L) :
    Function.Surjective (totalLinking L E Q) := by
  intro z
  let i : Fin n := ⟨0, L.nonempty⟩
  obtain ⟨x, hx⟩ := (exteriorLinkingCoordinates_bijective L E Q).2 (Pi.single i z)
  refine ⟨x, ?_⟩
  simp [totalLinking, hx]

end SeifertSurfaces.GenusLinking



-- Exact paid support transport; existing native declarations retain their values.
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
 let source := System.FilePath.mk (← getFileName)
 let mut dataConstants : Array ConstantInfo := #[]
 for payload in #["final_paid_cut_000.olean","final_paid_cut_001.olean","final_paid_cut_002.olean","final_paid_cut_003.olean","final_paid_cut_004.olean","final_paid_cut_005.olean","final_paid_cut_006.olean","final_paid_cut_007.olean","final_paid_cut_008.olean","final_paid_cut_009.olean","final_paid_cut_010.olean","final_paid_cut_011.olean","final_paid_cut_012.olean","final_paid_cut_013.olean","final_paid_cut_014.olean","final_paid_cut_015.olean","final_paid_cut_016.olean","final_paid_cut_017.olean","final_paid_cut_018.olean","final_paid_cut_019.olean","final_paid_cut_020.olean","final_paid_cut_021.olean","final_paid_cut_022.olean","final_paid_cut_023.olean","final_paid_cut_024.olean","final_paid_cut_025.olean","final_paid_cut_026.olean","final_paid_cut_027.olean","final_paid_cut_028.olean","final_paid_cut_029.olean","final_paid_cut_030.olean","final_paid_cut_031.olean","final_paid_cut_032.olean","final_paid_cut_033.olean","final_paid_cut_034.olean","final_paid_cut_035.olean","final_paid_cut_036.olean","final_paid_cut_037.olean","final_paid_cut_038.olean","final_paid_cut_039.olean","final_paid_cut_040.olean","final_paid_cut_041.olean","final_paid_cut_042.olean","final_paid_cut_043.olean","final_paid_cut_044.olean","final_paid_cut_045.olean","final_paid_cut_046.olean","final_paid_cut_047.olean","final_paid_cut_048.olean","final_paid_cut_049.olean","final_paid_cut_050.olean","final_paid_cut_051.olean","final_paid_cut_052.olean","final_paid_cut_053.olean","final_paid_cut_054.olean","final_paid_cut_055.olean","final_paid_cut_056.olean","final_paid_cut_057.olean","final_paid_cut_058.olean","final_paid_cut_059.olean","final_paid_cut_060.olean","final_paid_cut_061.olean","final_paid_cut_062.olean","final_paid_cut_063.olean","final_paid_cut_064.olean","final_paid_cut_065.olean","final_paid_cut_066.olean","final_paid_cut_067.olean","final_paid_cut_068.olean","final_paid_cut_069.olean","final_paid_cut_070.olean","final_paid_cut_071.olean","final_paid_cut_072.olean","final_paid_cut_073.olean","final_paid_cut_074.olean","final_paid_cut_075.olean","final_paid_cut_076.olean","final_paid_cut_077.olean","final_paid_cut_078.olean","final_paid_cut_079.olean","final_paid_cut_080.olean","final_paid_cut_081.olean","final_paid_cut_082.olean","final_paid_cut_083.olean","final_paid_cut_084.olean","final_paid_cut_085.olean","final_paid_cut_086.olean","final_paid_cut_087.olean","final_paid_cut_088.olean","final_paid_cut_089.olean","final_paid_cut_090.olean","final_paid_cut_091.olean","final_paid_cut_092.olean","final_paid_cut_093.olean","final_paid_cut_094.olean","final_paid_cut_095.olean","final_paid_cut_096.olean","final_paid_cut_097.olean","final_paid_cut_098.olean","final_paid_cut_099.olean","final_paid_cut_100.olean","final_paid_cut_101.olean","final_paid_cut_102.olean","final_paid_cut_103.olean","final_paid_cut_104.olean","final_paid_cut_105.olean","final_paid_cut_106.olean","final_paid_cut_107.olean","final_paid_cut_108.olean","final_paid_cut_109.olean","final_paid_cut_110.olean","final_paid_cut_111.olean","final_paid_cut_112.olean","final_paid_cut_113.olean","final_paid_cut_114.olean","final_paid_cut_115.olean","final_paid_cut_116.olean","final_paid_cut_117.olean","final_paid_cut_118.olean"] do
  let (d,_) ← liftIO <| readModuleData (source.parent.getD "." / "ProofData" / payload)
  dataConstants := dataConstants ++ d.constants
 let mut all : Std.HashMap Name ConstantInfo := {}
 for ci in dataConstants do all := all.insert ci.name ci
 let mut required : Std.HashSet String := {}
 for n in #["SeifertSurfaces.GenusLinking.MeridianConstruction.tubular_neighborhood_nonempty","SeifertSurfaces.GenusLinking.MeridianConstruction.positive_reframing","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knot_meridian_generates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_tube_meridian_class_eq","SeifertSurfaces.GenusLinking.componentLinking","SeifertSurfaces.GenusLinking.linkingWithKnot","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.disjointPairPole","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.disjointPairPole_misses_first","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.disjointPairPole_misses_second","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.SphereSpace","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplement","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplement._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complementGaussPairing","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_meridian_gauss_pairing_eq","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complementGaussPairing_pair_symmetric","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complementGaussPairing_meridian_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoHomology_zsmul_injective","SeifertSurfaces.GenusLinking.LinkIsLinkingIndecomposable","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanTube","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanTube_uniform_radius","SeifertSurfaces.GenusLinking.MeridianConstruction.scaleParameter","SeifertSurfaces.GenusLinking.MeridianConstruction.tubular_neighborhood_nonempty._simp_1_1","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanTube_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.scaleParameter_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.scaleParameter_openEmbedding","SeifertSurfaces.GenusLinking.MeridianConstruction.localHomeomorphOn_open_image","SeifertSurfaces.GenusLinking.MeridianConstruction.scaleParameter_rank","SeifertSurfaces.GenusLinking.MeridianConstruction.poleInverse","SeifertSurfaces.GenusLinking.MeridianConstruction.poleInverse_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.poleInverse_rank","SeifertSurfaces.GenusLinking.MeridianConstruction.poleInverse_openEmbedding","DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv","SeifertSurfaces.GenusLinking.MeridianConstruction.diskScaleEquiv","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanCore","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanTube_core","SeifertSurfaces.GenusLinking.MeridianConstruction.poleInverse_core","SeifertSurfaces.GenusLinking.MeridianConstruction.tubular_neighborhood_nonempty._simp_1_2","SeifertSurfaces.GenusLinking.MeridianConstruction.PositiveTubeFraming","SeifertSurfaces.GenusLinking.MeridianConstruction.tubeEuclideanExtension","SeifertSurfaces.GenusLinking.MeridianConstruction.tube_orientation_det_ne_zero","SeifertSurfaces.GenusLinking.MeridianConstruction.PositiveTubeFraming._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.reflectTube","SeifertSurfaces.GenusLinking.MeridianConstruction.reflected_tube_det_eq_neg","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.integralHomology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.curveClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridian","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PuncturedTubeDomain","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TubeImage","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedKnotMVIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.longitudeTubeCoordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.standardTubeCoordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTube_geometric_basis_generates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.fullTubeInclusion","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeInclusion","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actual_meridian_coordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.fullTube_meridian_class_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedKnotMVIso_curve","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeImageProjectionIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleFundamentalClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleFundamentalClass_generates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.curveClass_id","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeImageProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.fullTube_projection_longitude","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.HF","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.curveClass_postcomp","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeImageProjectionIso_hom","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_meridian_multiple_eq_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PositiveTubeFraming","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition","SeifertSurfaces.GenusLinking.MeridianConstruction.sphereExtension","SeifertSurfaces.GenusLinking.MeridianConstruction.parameter","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inverse","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_small_domain","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalTransition","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleVector","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedCircle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_coordinate_loop_homotopic_circle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivativeEquiv","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalTransition_derivative","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalTransition_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_normalDerivative_det","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleVector_norm","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridianRadius","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereExtension_normal_circle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianCoordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleVector_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PuncturedPlane","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeNormalCoordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeCoordinates_homotopic_standard","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.curveClass_tubeMeridian_eq_radius","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.curveClass_meridian_eq_coordinate_class","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.curveClass_homotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.disjointPairPole._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.disjoint_knot_pair_omits_point","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complementGaussPairing._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.KnotComplementWithoutPole","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.ComplementSet","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleOmissionHomologyIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricGaussPairing","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.joint_meridian_gauss_pairing_eq_of_derivative_sign","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_gauss_derivative_sign_independent","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotPairComplementCurve","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.twoKnotGaussClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complementGaussPairing_pair","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.twoKnotGaussClass_symmetric","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_uniform_pole_avoidance","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PuncturedMeridianSolidTorus","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.MeridianSolidTorus","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.MeridianDisk","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PuncturedMeridianSolidTorus._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.Punctured","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.normalizeMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.normalize_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedMeridianGaussExtension","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complementGaussPairing_meridian_boundary","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryClass_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedMeridianGaussExtension","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedMeridianGaussExtension_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoGenerator","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoGenerator_generates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoGenerator_zsmul_injective","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanTube._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalOne","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalTwo","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanTube_local_neighborhood","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanCore_injective","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanTube_core_compact","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanCore_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalOne_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalTwo_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.knotPole","SeifertSurfaces.GenusLinking.MeridianConstruction.pole_chart_target","DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv","DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv._proof_1_1","SeifertSurfaces.GenusLinking.MeridianConstruction.diskScaleEquiv._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.diskScaleEquiv._proof_2","SeifertSurfaces.GenusLinking.MeridianConstruction.diskScaleEquiv._proof_3","SeifertSurfaces.GenusLinking.MeridianConstruction.diskScaleEquiv._proof_4","SeifertSurfaces.GenusLinking.MeridianConstruction.diskScaleEquiv._proof_5","SeifertSurfaces.GenusLinking.MeridianConstruction.diskScaleEquiv._proof_7","SeifertSurfaces.GenusLinking.MeridianConstruction.knotPole._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.component_in_pole_chart","SeifertSurfaces.GenusLinking.MeridianConstruction.tubeEuclideanExtension_fderiv_injective","SeifertSurfaces.GenusLinking.MeridianConstruction.coordinate_vectors_independent","SeifertSurfaces.GenusLinking.MeridianConstruction.tubeEuclideanExtension_fderiv_orthogonal","SeifertSurfaces.GenusLinking.MeridianConstruction.reflectTube._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.domainReflection","SeifertSurfaces.GenusLinking.MeridianConstruction.reflectTube._proof_2","SeifertSurfaces.GenusLinking.MeridianConstruction.reflectTube._proof_4","SeifertSurfaces.GenusLinking.MeridianConstruction.reflectTube._proof_5","SeifertSurfaces.GenusLinking.MeridianConstruction.reflectTube._proof_6","SeifertSurfaces.GenusLinking.MeridianConstruction.ambientExtension","SeifertSurfaces.GenusLinking.MeridianConstruction.extension_local","SeifertSurfaces.GenusLinking.MeridianConstruction.coordinateReflection","SeifertSurfaces.GenusLinking.MeridianConstruction.reflected_extension_fderiv_eq","SeifertSurfaces.GenusLinking.MeridianConstruction.coordinateReflection_basis","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.integralChains._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.integralHomology._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridianPoint","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridian_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TubeImage._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.homeoHomologyIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusSection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFirstCircle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleVector_mem_disk","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleVector_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.standardTubeCoordinates._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusHomologyIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.Torus","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusSecondCircle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torus_geometric_basis_generates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTube_projection_longitude","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTube_projection_meridian","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeImageHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.fullTubeInclusion._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.fullTubeInclusion._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubePointMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubePointMap_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.fullTube_projection_meridian","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.curveClass_constant","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeProjectionHomologyIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.integralChains._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.integralChains","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleFundamentalClass._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLoopChain","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleFundamentalClass._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLoopChain_boundary","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeImageProjection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.radialHomologyIso._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.radialHomologyIso._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeProjectionHomologyIso._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeProjectionHomologyIso._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTube_geometric_basis_independent","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeEuclideanExtension","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLoopSimplex._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coordinateLog","SeifertSurfaces.GenusLinking.MeridianConstruction.sphereExtension._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.diskParameter","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inverse._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inverse._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_smooth","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereExtension_core","SeifertSurfaces.GenusLinking.MeridianConstruction.sphereExtension_smooth","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_parameter_local","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedCircle._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.local_normal_circle_linearization","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.linearCircle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_linearCircle_homotopic","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivativeEquiv._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivativeEquiv._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivative","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivativeEquiv._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivativeEquiv._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normal_derivative_frame_det_relation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridianRadius._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridianRadius._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.scaled_circleVector_mem_disk","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridianRadius._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridianRadius._proof_4","SeifertSurfaces.GenusLinking.MeridianConstruction.diskParameter._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianNormal._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianNormal._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianCoordinates._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeNormalCoordinates._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeNormalCoordinates._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizeTubeCoordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizeTubeCoordinates_homotopic","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.unitTubeCoordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.unitNormal","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.unitNormal_mem","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.unitNormal_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.unitNormal_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.unitTubeCoordinates_circle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridianRadius_one","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridianRadius_homotopic","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubePointMap_meridianCoordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.disjoint_knot_pair_omits_point._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleOmissionHomologyIso._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleOmissionInclusion","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleOmissionInclusion_H1_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricGaussPairing._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricCirclePrism","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussSphereMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDifference","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.joint_meridian_gauss_calibration","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartFrameMatrix","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.chartTubeExtension","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positiveGaussDerivative_poleFrame_sign","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartFrame_det_negative_sign_independent","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotPairComplementCurve._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotPairComplementCurve._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.twoKnotGaussSphereMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusPrismClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complementGaussPairing_curve","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.pairCurveInComplement","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereAntipode","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.twoKnotGaussClass_swap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoAntipode_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.diskZero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.UnitSphere","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.normalizeMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianDiskPoint._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallNormalDisk._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianGaussExtension","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedMeridianGaussExtension._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedMeridianGaussExtension._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryTorus","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleAvoidingMeridian","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complementGaussPairing_meridian_torus","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusPrismClass_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryTorus_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedMeridianGaussExtension._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedMeridianGaussExtension._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedMeridianGaussExtension._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterRegion","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterBall_exists","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.scaledNonzeroSphere","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalSphere_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.localMeridianSphereMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianGaussExtension_localSphere","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.localMeridianSphereMap_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoCircleHomologyIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoGenerator_calibration","SeifertSurfaces.GenusLinking.MeridianConstruction.normalDirection","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalOne._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanVelocity","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanCross","SeifertSurfaces.GenusLinking.MeridianConstruction.liftedTube","SeifertSurfaces.GenusLinking.MeridianConstruction.liftedTube_localInverse","SeifertSurfaces.GenusLinking.MeridianConstruction.tubeParameter","SeifertSurfaces.GenusLinking.MeridianConstruction.tubeParameter_localHomeomorph","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanTube_rank_of_lifted_rank","SeifertSurfaces.GenusLinking.MeridianConstruction.liftedTube_fderiv_injective_on_inverse_source","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanVelocity_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanVelocity_ne_zero","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanCross_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.knot_omits_point","SeifertSurfaces.GenusLinking.MeridianConstruction.instFactEqNatFinrankRealEucOfNatHAdd_globalTubeConstruction","extChartAtPartialDiffeomorph","DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_hasFDerivAt","_private.DifferentialGeometry.Topology.Manifold.ImmersionCriterion.0.DifferentialGeometry.Topology.Manifold.modelInverse","SeifertSurfaces.GenusLinking.MeridianConstruction.diskScaleEquiv._proof_6","SeifertSurfaces.GenusLinking.MeridianConstruction.instFactEqNatFinrankRealEucOfNatHAdd_knotPlacement","SeifertSurfaces.GenusLinking.MeridianConstruction.component_in_pole_chart._simp_1_1","SeifertSurfaces.GenusLinking.MeridianConstruction.component_in_pole_chart._simp_1_2","SeifertSurfaces.GenusLinking.MeridianConstruction.knotPole_not_on_knot","SeifertSurfaces.GenusLinking.MeridianConstruction.ambientExtension_fderiv_injective","SeifertSurfaces.GenusLinking.MeridianConstruction.ambientExtension_contDiffAt","SeifertSurfaces.GenusLinking.MeridianConstruction.ambientExtension_norm_sq","SeifertSurfaces.GenusLinking.MeridianConstruction.ambientExtension_core","SeifertSurfaces.GenusLinking.MeridianConstruction.diskReflection","SeifertSurfaces.GenusLinking.MeridianConstruction.tube_reflection_immersion","SeifertSurfaces.GenusLinking.MeridianConstruction.reflectTube._proof_3","SeifertSurfaces.GenusLinking.MeridianConstruction.normalReflection","SeifertSurfaces.GenusLinking.MeridianConstruction.diskReflection._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.coordinateReflection._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.ambient_reflect_local","SeifertSurfaces.GenusLinking.MeridianConstruction.coordinateReflection_apply","SeifertSurfaces.GenusLinking.MeridianConstruction.normalReflection._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.normalReflection._proof_2","SeifertSurfaces.GenusLinking.MeridianConstruction.normalReflection_involutive","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_meridian_misses_core","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_10","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_11","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplement_open","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_complement_cover","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusSection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusSection._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusSection._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFirstCircle._proof_1","CurveComplexGenusTwo.CWHurewicz.singularHomologyIsoOfHomotopyInverse","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusHomologyIso._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusHomologyIso._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusHomologyIso._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusHomologyIso._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusSecondCircle._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFundamentalClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFundamentalClass_generates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFundamentalClass_first","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFundamentalClass_second","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalCircle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorusProjection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.longitudeTubeCoordinates.eq_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorus_retraction","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianTubeCoordinates_eq","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeImageHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubePointMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.contractible_homology_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreSection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeProjectionHomologyIso._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeProjectionHomologyIso._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLoopSimplex","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLoopSimplex._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLoopSimplex._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeProjection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torus_geometric_basis_independent","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLog","SeifertSurfaces.GenusLinking.MeridianConstruction.diskParameter_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inverse_core","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coordinateLog_smooth","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inverse_smoothAt","SeifertSurfaces.GenusLinking.MeridianConstruction.parameter_smooth","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inverse_continuousAt","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.parameter_coordinateLog_local","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.local_normal_linearization_bound","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.punctured_normal_segment_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.scaled_circleVector_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.linearCircle._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.linearCircle._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.linearCircle_radius_homotopic","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_planar_circle_homotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivative._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivative._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivative_bijective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalDerivativeEquiv._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLog_one","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_derivative_relation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_derivative_core","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.parameter_coordinate_decomposition","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normal_block_det","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_point_misses_core","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inverse_normal_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeNormalCoordinates._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizeTubeCoordinates._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizeTubeCoordinates._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizeTubeCoordinates._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.radial_norm_lt_two","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.radial_scale_positive","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.unitTubeCoordinates._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.unitNormal_norm","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_inverse","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleOmissionInclusion._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.ChartBallInComplement","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.chartBallInComplement_exists","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PoleRemovedSet","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PoleBallSet","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallSet_open","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBall_cover","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.EuclideanBall","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanBall_contractible","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallImageHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PuncturedEuclideanBall","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedEuclideanBall_homology_one_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemoved_inclusion","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.cover_inclusion_H1_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedEuclideanBall_pathConnected","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_homologyShift","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricCirclePrism._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleBasedInclusion","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricSingularHomotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positiveCircleLoopHomotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartKnot._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussSphereMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussDifference","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalDifference","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.localMeridianSphereClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianGaussExtension_localSphereClass_signed","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryClass_local_calibration","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverseAmbient","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeFrameMatrix","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.chartTubeEuclideanDerivative","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDifference_det_relation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeFrameMatrix_det_pole_relation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartFrameMatrix_det_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartFrame_det_sign_independent","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleOmissionHomologyIso_curve","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complementGaussPairing_lift","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricGaussPairing_curve","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.pairCurveInComplement._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.pairCurveInComplement._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereAntipode._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusSwap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.twoKnotGaussSphereMap_swap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusPrismClass_swap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoPole","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.antipodal_open_cover","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.mvConnecting_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.punctured_contractible","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverIntersectionSwap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverIntersectionSwap_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverRestrictedMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverIntersectionMapsTo","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actualMVConnecting_map","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actualMVConnecting_swap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapAntipode","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapAntipode_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.diskZero._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianDiskChart","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartKnot","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianGaussExtension._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianGaussExtension_eq_zero_iff","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedMeridianGaussExtension._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryTorus._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryTorus._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryTorus._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.scaled_circle_mem_smallDisk","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleAvoidingMeridian._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleAvoidingMeridian._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleAvoidingMeridian._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleAvoidingMeridian._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleAvoidingMeridian._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleOmission_poleAvoidingMeridian","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusCupHomologyMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusCupHomologyMap_prism","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PuncturedSmallBall","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalSet","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryProduct","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryProduct_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalInclusion_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterRegion._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleExpChart","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeNormalProject","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterRegion_open","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterRegion_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.scaledNonzeroSphere._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDifference_smooth","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.local_sphere_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDerivativeEquiv","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDifference_hasFDerivAt","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDifference_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusParameterMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialSection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianGaussExtension_parameter","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialSection_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusParameterMap_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.sphereSuspensionIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoCircleHomologyIso._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph","SeifertSurfaces.GenusLinking.MeridianConstruction.exists_direction_off_tangents","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanCross._proof_1","DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv","SeifertSurfaces.GenusLinking.MeridianConstruction.frameEquiv","SeifertSurfaces.GenusLinking.MeridianConstruction.liftedTube_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.liftedTube_derivative","SeifertSurfaces.GenusLinking.MeridianConstruction.tubeParameter_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.coreRotation_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanVelocity_exp","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanLift_fderiv_injective","SeifertSurfaces.GenusLinking.MeridianConstruction.knot_omits_point._proof_1_1","DifferentialGeometry.PartialDiffeomorph.extChartAt","DifferentialGeometry.Topology.Manifold.isImmersionAtOfComplement_of_hasFDerivAt","_private.DifferentialGeometry.Topology.Manifold.ImmersionCriterion.0.DifferentialGeometry.Topology.Manifold.modelInverse._proof_1","_private.DifferentialGeometry.Topology.Manifold.ImmersionCriterion.0.DifferentialGeometry.Topology.Manifold.modelInverse._proof_2","_private.DifferentialGeometry.Topology.Manifold.ImmersionCriterion.0.DifferentialGeometry.Topology.Manifold.modelInverse._proof_3","SeifertSurfaces.GenusLinking.MeridianConstruction.ambientExtension_mfderiv_injective","SeifertSurfaces.GenusLinking.MeridianConstruction.ambientExtension_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.diskReflection._proof_3","SeifertSurfaces.GenusLinking.MeridianConstruction.diskReflection._proof_4","SeifertSurfaces.GenusLinking.MeridianConstruction.diskReflection._proof_5","SeifertSurfaces.GenusLinking.MeridianConstruction.normalReflection_mem","SeifertSurfaces.GenusLinking.MeridianConstruction.diskParameter_reflection_local","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inverse_tube","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_complement_cover._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_complement_cover._simp_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.knotComplementMVIso._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.threeSphere_homology_two_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.threeSphere_homology_one_zero","CurveComplexGenusTwo.CWHurewicz.singularHomologyIsoOfHomotopyInverse._proof_1","CurveComplexGenusTwo.CWHurewicz.singularHomologyIsoOfHomotopyInverse._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeTorus_deformation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFundamentalClass._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFundamentalClass._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopChain","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFundamentalClass._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopChain_boundary","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusWindingChainMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torus_cycles_generate","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusEdgeClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopEdge","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFundamentalClass_homologyι","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.curveClass_homologyι","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopSimplex","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusPeriod._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusPeriod","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineEdge._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.TorusOp1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.TorusOp1._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.TorusOp1._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.TorusSSet","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torus_pOpcycles_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planeToComplex","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalCircle._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalCircle_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalCircle_circleVector","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.contractible_homology_zero._proof_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreSection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreHomotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFirstProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusSecondProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.firstProjection_first","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.firstProjection_second","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.secondProjection_first","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.secondProjection_second","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLog_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.diskParameter_smooth","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleExp_circleLog_local","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.diskParameter_val","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.local_normal_linearization_bound._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.punctured_normal_segment_ne_zero._abel_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexToPlane","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexToPlane_one","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planeToComplex_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexToPlane_I","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexLinearPart","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexAntilinearPart","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complex_linear_positive_dominates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complex_linear_decomposition","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complex_antilinear_segment_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedComplexToPlane","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexToPlane_planeToComplex","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planeToComplex_circleVector","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_derivative_longitudinal","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_derivative_bijective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleExpChart_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleExpChart_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_reconstruct_local","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeTransition_core_local","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.plane_coordinate_decomposition","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizeTubeCoordinates._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizeTubeCoordinates._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.unitNormal.eq_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_11","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.puncturedChart","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedChart_symm_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.chartBallInComplement_exists._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.chartBallInComplement_exists._simp_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.PoleRemovedSet._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallMap_openEmbedding","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBall_cover._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBall_cover._simp_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallMap_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanBallHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallImageHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.sphere_first_homology_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedEuclideanBall_homology_one_zero._proof_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedEuclideanBallHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.radialHomologyIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_11","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_13","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallMap_ne_pole_iff","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_10","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_12","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.H0_inclusion_injective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_cycleLift._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_cycleLift._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_homologyShift._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_homologyShift._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_cycleLift._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_cycleLift","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_boundaries_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleBasedInclusion._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricSingularHomotopyMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricSingularHomotopy._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricSingularHomotopy._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricSingularHomotopy._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positiveCircleLoopHomotopy._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positiveCircleLoopHomotopy._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positiveCircleLoopHomotopy._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positiveCircleLoopHomotopy._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartComplement","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussDifference._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussDifference._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalSphere_homology_signed","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.localMeridianSphereClass_generates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverseSphere","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeFrameMatrix._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeFrameMatrix._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.chartTubeEuclideanDerivative._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeTimeReflection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDifference_derivative_relation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeTimeReflection_det","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeFrameMatrix","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeFrameMatrix_pole_comparison","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeFrameMatrix_comp_det","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.three_standard_vectors_independent","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverseAmbient_fderiv_injective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverseAmbient_fderiv_orthogonal","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartFrame_det_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartFrame_det_sign_independent._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartFrame_det_sign_independent._simp_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricCirclePrism_naturality","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circlePrismChain","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusPrismClass_homologyι","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circlePrismChain_swap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoPole._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereTwoPole._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.antipodal_open_cover._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.antipodal_open_cover._simp_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.antipodal_open_cover._simp_1_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.antipodal_open_cover._simp_1_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.mvConnecting_isIso._proof_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverIntersectionSwap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverIntersectionSwap._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverRestrictedMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverRestrictedMap._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actualOpenCoverHomologyIso_connecting_assoc","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverIntersectionMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverSmallMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvConnecting_map_assoc","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actualOpenCoverHomologyIso_map_assoc","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actualOpenCoverHomologyIso_connecting","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvIntersectionSwap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvSmallSwap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvConnecting_swap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actualOpenCoverHomologyIso_swap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapAntipode._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapAntipode._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapNormalizationIsoTwo","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapNormalizationTwo","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOneAntipode","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapAntipode_normalize","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOneAntipode_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapNormalizationIsoTwo_hom","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianDiskPoint","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianDiskChart._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianDiskChart._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallNormalDisk","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianDiskChart._simp_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartKnot._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartKnot._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeMeridianRadius_misses_pole","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusCupOpcyclesMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusCupOpcyclesMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusCupOpcyclesMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusCupChainMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusCupOpcyclesMap._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusCupChainMap_boundary","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circlePrismTriangle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circlePrismChain_triangles","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusWindingCup","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.simplex_torusCupChainMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusWindingCup_prism_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusWindingCup_prism_one","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_10","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_13","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryProduct._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryProduct._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianBoundaryProduct._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialProductSection_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcSet","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.MeridianEastArc","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianDisk_contractible","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianEastArc_contractible","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalInclusion_homology_isIso._proof_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSmallDisk_higher_homology_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalInclusion_homology_isIso._proof_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionProjection_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.cover_inclusion_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalSet_open","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcSet_open","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorus_cover","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleExpChart._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeNormalEmbed._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.chartTubeExtension_smooth","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.scaledLinearSphere","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.local_three_dimensional_sphere_linearization","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDerivativeEquiv._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesEquiv._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesEquiv._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDerivativeEquiv._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDerivativeEquiv._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDifference_derivative","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalDifference_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusParameterMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusParameterMap._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialSection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialSection._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialSection._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedChart_eq_chartAt","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereExtension_normal_small","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereExtension_longitudinal","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomologyIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SolidTorusRemovedSet","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SolidTorusLocalBallSet","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SolidTorusRemovedSet._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterMap_openEmbedding","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusLocalBall_cover","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusLocalBallHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusParameterMap_homology_isIso._proof_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.cover_local_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorus_higher_homology_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusParameterMap_homology_isIso._proof_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusParameterMap_homology_isIso._proof_1_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.sphereSuspensionIso._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.sphereSuspensionIso._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.sphereSuspensionIso._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.sphereSuspensionIso._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_10","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_11","SeifertSurfaces.GenusLinking.MeridianConstruction.tangentCone","SeifertSurfaces.GenusLinking.MeridianConstruction.tangentCone_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.tangentCone_det_zero","SeifertSurfaces.GenusLinking.MeridianConstruction.tangentCone._proof_1","DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero","SeifertSurfaces.GenusLinking.MeridianConstruction.frameEquiv._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.frameEquiv._proof_2","SeifertSurfaces.GenusLinking.MeridianConstruction.frameEquiv._proof_3","SeifertSurfaces.GenusLinking.MeridianConstruction.frameLinear","SeifertSurfaces.GenusLinking.MeridianConstruction.frameEquiv._proof_4","SeifertSurfaces.GenusLinking.MeridianConstruction.frameEquiv._proof_6","SeifertSurfaces.GenusLinking.MeridianConstruction.frameLinear._proof_4","SeifertSurfaces.GenusLinking.MeridianConstruction.frameLinear._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.frameLinear._proof_2","SeifertSurfaces.GenusLinking.MeridianConstruction.frameLinear._proof_3","SeifertSurfaces.GenusLinking.MeridianConstruction.frameLinear._proof_5","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanLift_smooth","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanCore_mfderiv_injective","SeifertSurfaces.GenusLinking.MeridianConstruction.circleExp_mfderiv_injective","DifferentialGeometry.PartialDiffeomorph.extChartAt._proof_1","SeifertSurfaces.GenusLinking.MeridianConstruction.parameter_mfderiv_injective","SeifertSurfaces.GenusLinking.MeridianConstruction.diskReflection._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedTubeHomeomorph._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.threeSphere_homology_two_zero._proof_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.threeSphere_homology_one_zero._proof_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleVector_normalCircle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusEdgeGeneratorMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusEdgeWinding","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusEdgeGeneratorMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusRayMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopClassHom","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torus_generator_boundary_relation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusEdgeGenerator_eq_pOpcycles","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusRayMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusRayMap._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineEdge","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopChain.eq_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLoopChain.eq_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planeToComplex._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planeToComplex._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planeToComplex._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planeToComplex_norm","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreHomotopy._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreHomotopy._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreHomotopy._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreHomotopy._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleExpChart_one","SeifertSurfaces.GenusLinking.MeridianConstruction.diskParameter_local","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexToPlane._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexToPlane._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexToPlane._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexToPlane_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complex_linear_norm_difference","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedComplexToPlane._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedComplexToPlane._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleLog_circleExp_local","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.puncturedChart._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.puncturedChart._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.puncturedChart._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.puncturedChart_antipode","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallMap._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanBallHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanBallHomeomorph._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanBallHomeomorph_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.sphereIncl","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.sphereIncl_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.radialHomologyIso._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.radialHomologyIso._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.radialHomologyIso._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_10","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedPoleBallHomeomorph._proof_12","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleRemovedHomeomorph._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.augmentation_naturality","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_homologyShift._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_cycleLift._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_cycles_closed","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_degree_two_relation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_cycleLift.eq_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.intervalLoopSSetMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricSingularHomotopyMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricSingularHomotopyMap_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.intervalLoopSSetMap_const","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartComplement._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartComplement._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChart_difference_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.local_sphere_homology_signed","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeTimeReflection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeTimeReflection._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeTimeReflection._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeTimeReflection._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeTimeReflection._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.timeReflection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalDifference_derivative","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates_timeReflection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanMatrix_det","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeFrameMatrix._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverse_chartTube_core","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeEuclideanExtension_pole_derivative","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.three_vector_decomposition","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.instFactEqNatFinrankRealEucOfNatHAdd_poleChartOrientationGeometry","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverseSphere_smooth","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverseAmbient_contDiffAt","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverseAmbient_norm_sq","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleChartFrameMatrix_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_homologyShift_naturality","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricCircleHomotopy_naturality_h","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circlePrismChain._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inclusionChainMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circlePrismHomotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_homologyShift_cycles_assoc","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circlePrismTriangle_swap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverIntersectionSwap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverRestrictedMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallPush","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverSmallMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvConnecting_map","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actualOpenCoverHomologyIso_map","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallSwap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvSmallSwap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvSwapSequence","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvSmallSwap_inclusion","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapNormalizationTwo._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapNormalizationTwo._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOneAntipode._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.stereographicNormalCoordinates","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedChart_formula","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalize_pos_smul_vector","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedChart_scalar_positive","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.stereographicNormalCoordinates_neg","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleAntipode","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleAntipode_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.meridianDiskPoint._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallNormalDisk._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallNormalDisk._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusCupChainMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.CupTorusSSet","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusWindingCup_boundary","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusFirstWinding","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusWindingCup._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusSecondWinding","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.cupFirstProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.cupSecondProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.cupFirstProjection_prism","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.cupSecondProjection_prism","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.singularWinding_degenerate","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_11","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalHomeomorph._proof_12","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialProductHomologyIso","CircleCoverGeometry.eastArc_contractible","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_10","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_13","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circle_higher_homology_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionProjection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionProjection._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.product_right_contractible_projection_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalProjection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalProjection._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_core_in_pole_chart","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.scaledLinearSphere._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.scaledLinearSphere._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.local_three_dimensional_linearization_bound","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.punctured_three_dimensional_segment_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedLinearHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere_homology_isIso._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalEuclideanDifference_derivative_bijective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesEquiv._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterMap._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusParameterMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterMap_ne_core_iff","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusParameterMap._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.instFactEqNatFinrankRealEucOfNatHAdd_meridianGaussLocalComparison","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomologyIso._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomologyIso._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomologyIso._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomologyIso._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterMap_injective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanSolidTorusParameter","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanSolidTorusParameter_isOpenMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusLocalBall_cover._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusLocalBall_cover._simp_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterMap_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusLocalBallHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_10","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_12","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusProjection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusProjection_homology_isIso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_10","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_11","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanCircleHomeomorph._proof_9","SeifertSurfaces.GenusLinking.MeridianConstruction.tangentCone_derivative_kills","SeifertSurfaces.GenusLinking.MeridianConstruction.frameLinear_bijective","SeifertSurfaces.GenusLinking.MeridianConstruction.frameEquiv._proof_5","SeifertSurfaces.GenusLinking.MeridianConstruction.diskParameter_mfderiv_injective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFirstEdge","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusSecondEdge","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusRayMap._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusRayMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusPointRayClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusEdgeGeneratorMap_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusGeometricEdge_winding","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusRayMap_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusWindingChainMap_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreHomotopy._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreHomotopy._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreHomotopy._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tubeCoreHomotopy._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.complexToPlane_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleBallMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.euclideanBallHomeomorph_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.sphereIncl._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.normalize_incl","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.radialHomotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.HF0","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.RZ","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.hzero_ext","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.pointClass","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.pointClass_map","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.pointClass._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.HF0._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.pointClass._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.pointClass._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.pointClass._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_degree_one_relation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.intervalLoopSimplex","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.singular_product_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.intervalLoopSSetMap_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.linear_sphere_homology_signed","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverse_chartTube_local","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.poleInverseAmbient_contDiff","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.selfHomotopy_homologyShift_cycles","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricSingularHomotopy_h_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.inclusionChainMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circlePrismTriangle_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallPush._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallPush._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverSmallMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallPush_boundary","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverSequenceMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actualOpenCoverHomologyIso_map._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.actualOpenCoverHomologyIso_map._simp_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverSmallMap_inclusion","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallSwap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallSwap._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallSwap._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvSmallSwap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvPairSwap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvIntersectionSwap_difference","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvPairSwap_sum","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.stereographicNormalCoordinates._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphere_finrank_fact","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.stereographicNormalCoordinates._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.stereographicNormalCoordinates._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleAntipode._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleAntipode_class","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallNormalDisk._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusFirstWinding_boundary","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusSecondWinding_boundary","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialProductHomologyIso._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialProductHomologyIso._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialProductHomologyIso._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialProductHomologyIso._proof_4","CircleCoverGeometry.eastArc","CircleCoverGeometry.eastArcHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_11","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusArcHomeomorph._proof_12","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circle_higher_homology_zero._proof_1_1","CircleCoverGeometry.westArc","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circle_higher_homology_zero._proof_1_2","CircleCoverGeometry.westArc_contractible","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circle_higher_homology_zero._proof_1_3","CircleHomologyComputation.homotopyHomologyIso","CircleHomologyComputation.overlapHomotopyEquiv","CircleCoverGeometry.eastArc_open","CircleCoverGeometry.westArc_open","CircleCoverGeometry.arcs_cover","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionProjection._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_10","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_13","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_16","CurveComplexGenusTwo.CWHurewicz.singularHomologyMap_isIso_of_retraction","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusNormalProjection._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.instFactEqNatFinrankRealEucOfNatHAdd_gaussLocalDifferential","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_core_in_pole_chart._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.tube_core_in_pole_chart._simp_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.local_three_dimensional_linearization_bound._simp_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.punctured_three_dimensional_segment_ne_zero._abel_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedLinearHomeomorph._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.gaussLocalDifference_derivative_bijective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesEquiv","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusParameterMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialProjection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallToPunctured","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadial_retraction","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeNormalEmbed","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.three_coordinate_decomposition","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusLocalHomeomorph._proof_11","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.solidTorusProjection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.overlapChart._proof_8","SeifertSurfaces.GenusLinking.MeridianConstruction.tangentCone_derivative","SeifertSurfaces.GenusLinking.MeridianConstruction.frameLinear_injective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusFirstEdge._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusSecondEdge._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusArg","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineEdge_period_shift","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineEdge_triangle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLog","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusGeometricEdge_relation","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLog_first","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLog_last","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusGeometricEdge_winding._abel_1_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopEdge_multiples","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planeToComplex_complexToPlane","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.deform","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.deform_continuous","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.radialHomotopy._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.radialHomotopy._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.HF0._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.pointClass_iso","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.intervalLoopSimplex._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.intervalLoopSimplex._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.intervalLoopSimplex._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.intervalLoopSSetMap.eq_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_linear_sphere_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.negative_linear_sphere_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.geometricSingularHomotopy_h","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circlePrismTriangle.eq_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.prism_interval_simplex","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallPush_mem","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverSequenceMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverPairMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverIntersectionMap_difference","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverPairMap_sum","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallChains_swap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallSwap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSmallSwap._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvPairSwap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverIntersectionSwap_subset","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleAntipodeHomotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusFirstWinding_boundary._simp_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.torusSecondWinding_boundary._simp_1_2","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.ImagAxis","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.eastStereo","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.imagAxisHomeomorph","CircleCoverGeometry.westArcHomeomorph","_private.CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers.0.CircleHomologyComputation.HF'","CircleHomologyComputation.homotopyHomologyIso._proof_1","CircleHomologyComputation.homotopyHomologyIso._proof_2","CircleCoverGeometry.upperArc","CircleCoverGeometry.lowerArc","CircleCoverGeometry.intersectionHomeomorph","CircleHomologyComputation.sumHomotopyEquiv","CircleHomologyComputation.overlapHomotopyEquiv._proof_1","CircleHomologyComputation.overlapHomotopyEquiv._proof_2","CircleCoverGeometry.arcs_cover._simp_1_3","CircleCoverGeometry.arcs_cover._simp_1_4","CircleCoverGeometry.arcs_cover._simp_1_5","CircleCoverGeometry.arcs_cover._simp_1_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_11","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_12","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_14","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.puncturedSolidTorusIntersectionHomeomorph._proof_15","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.chartTubeExtension_fderiv_injective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.timeReflection_bijective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesEquiv._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesEquiv._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesEquiv._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallToPunctured._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallToPunctured._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._proof_6","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._proof_9","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesInverse","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeNormalEmbed_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeNormalProject_apply","SeifertSurfaces.GenusLinking.MeridianConstruction.frameLinear_apply","SeifertSurfaces.GenusLinking.MeridianConstruction.globalFrame_independent","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineTriangle","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineTriangle_face_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineTriangle_face_one","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineTriangle_face_two","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusEdgeClass_boundary","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusGeometricEdge_relation._abel_1_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopEdge_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopEdge_add","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.scale","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.deform._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.intervalLoopSimplex._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_sphere_linear_alignment","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_pole_sphere_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere_comp","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.negativeIdentityEquiv","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.negativeIdentityEquiv_det","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere_negativeIdentity","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverPairPush","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverPairMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverSubsetPush_map","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverOrdinaryPush_map","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.singularFinsuppPush_comp","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleAntipodeHomotopy._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleAntipodeHomotopy._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.circleAntipodeHomotopy._proof_3","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.eastStereo._proof_1","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.imagAxisHomeomorph._proof_1","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.imagAxisHomeomorph._proof_3","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.imagAxisHomeomorph._proof_4","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.imagAxisHomeomorph._proof_5","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.imagAxisHomeomorph._proof_6","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.westToEast","_private.CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers.0.CircleHomologyComputation.HF'._proof_1","_private.CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers.0.CircleHomologyComputation.HF'._proof_2","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.componentInclusion","CircleCoverGeometry.intersectionHomeomorph._proof_1","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.componentInclusion_range","CircleHomologyComputation.sumHomotopyEquiv._proof_1","CircleHomologyComputation.sumHomotopyEquiv._proof_2","CircleHomologyComputation.sumHomotopyEquiv._proof_3","CircleHomologyComputation.sumHomotopyEquiv._proof_4","CircleCoverGeometry.upperArc_contractible","CircleCoverGeometry.lowerArc_contractible","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereExtension_mfderiv_injective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates_left_inv","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinates_right_inv","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallToPunctured._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._simp_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadial_norm","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadial_scale_positive","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._proof_5","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadialHomotopy._proof_8","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesInverse._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesInverse._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesInverse._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesInverse._proof_4","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalOne_ne_zero","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalTwo_ne_zero","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalOne_orthogonal","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalTwo_orthogonal_velocity","SeifertSurfaces.GenusLinking.MeridianConstruction.globalNormalTwo_orthogonal_one","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineTriangle._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torus_singular_face_eq","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopEdge.eq_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusAffineEdge_constant_class","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusPeriod_add","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.TorusHomologyConstruction.torusLoopEdge_add._abel_1_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.SphereHomologyConstruction.scale_pos","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.hyperplaneReflectionEquiv","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereReflection_alignment","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereSecondPole","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereSecondPole_reflection_fixes_first","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.hyperplaneReflectionEquiv_det","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere_reflection_pair_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_pole_sphere_homotopic_id","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.mvCoverPairMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.coverPairPush_boundary","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.imagAxisHomeomorph._proof_2","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.westToEast._proof_1","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.westToEast._proof_2","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.westToEast._proof_4","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.westToEast._proof_6","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.westToEast._proof_7","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.westToEast._proof_8","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.componentInclusion_openEmbedding","CircleCoverGeometry.intersection_split","CircleHomologyComputation.sumHomotopy","CircleCoverGeometry.upperArcHomeomorph","CircleCoverGeometry.lowerArcHomeomorph","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.smallBallRadial_norm._simp_1_1","SeifertSurfaces.GenusLinking.MeridianConstruction.normalDirection_off_tangents","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanCross_orthogonal_left","SeifertSurfaces.GenusLinking.MeridianConstruction.euclideanCross_orthogonal_right","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.hyperplaneReflectionEquiv._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.hyperplaneReflectionEquiv._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereDirection_span","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereSecondPole._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereSecondPole._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedLinearSphere_reflection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection_pair_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeNormalBlock","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.three_normal_block_injective","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planarLinearMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.three_pole_block_decomposition","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockMap.eq_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockMap_nonzero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedNonzeroMap","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedNonzeroMap_homotopic","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.three_positive_block_sphere_homotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.three_normal_block_positive_det","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.westToEast._proof_3","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.westToEast._proof_5","CircleCoverGeometry.upperArc_open","CircleCoverGeometry.lowerArc_open","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.componentInclusion_injective","CircleHomologyComputation.sumHomotopy._proof_1","CircleHomologyComputation.sumHomotopy._proof_2","CircleHomologyComputation.sumHomotopy._proof_3","CircleHomologyComputation.sumHomotopy._proof_4","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.upper_subset_east","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.east_im_pos_iff","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.lower_subset_east","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.east_im_neg_iff","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeNormalProject_embed","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planarLinearMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesInverse_zero_normal","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedNonzeroMap._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedNonzeroMap._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedNonzeroMap._proof_4","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planarComplexMultiplication","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.positive_planar_linear_first","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planar_linear_last","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockHomotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockHomotopy_nonzero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.three_positive_scalar_sphere_homotopy","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.three_pole_block_det","CircleCoverGeometry.components_disjoint","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_1","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_2","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_3","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_5","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_8","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_9","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_10","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.east_inverse_im","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection_pole","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection_neg","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection_involutive","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapReflection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapReflection_homology","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeCoordinatesInverse_apply","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.normalizedNonzeroMap._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planarComplexMultiplication._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.planeToComplex_ne_zero","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockHomotopy._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockHomotopy._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeBlockHomotopy._proof_3","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.threeNormalEmbed_single","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_4","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_6","_private.CurveComplexGenusTwo.Topology.CircleCoverGeometry.0.CircleCoverGeometry.subsetLiftHomeomorph._proof_7","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapReflection._proof_1","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapReflection._proof_2","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereOverlapReflection_normalize","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.stereographicNormalCoordinates_reflection","SeifertSurfaces.GenusLinking.PositiveMeridianConstruction.sphereHyperplaneReflection_formula","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.spanning_original_final","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.component_original_final","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.spanning_boundary_homology_of_filling","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.actual_oriented_boundary_filling","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.component_boundary_homology_of_filling","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.exists_total_disconnected_boundary_triangulation","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeBoundaryEdge","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrderedEdgeMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeCoefficient","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedFaceSignG","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_boundary_oriented_lifts","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeSingular","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_circle_assembly","SeifertSurfaces.GenusLinking.Continuation.component_filling_from_total","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.partialTriangulation_finite_disjoint_union","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.exists_component_triangulation","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.chartOrientationCoefficient._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTriangleEdge","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._aux_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._aux_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._proof_5","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._proof_6","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._proof_7","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._proof_8","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._aux_9","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._aux_11","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._aux_13","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._proof_15","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._aux_16","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._aux_18","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._aux_20","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._proof_22","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._proof_23","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricPartialVertexLinearOrder._proof_24","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedFaceSign","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedFaceSignG._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_boundary_edge_lifts","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeCoefficient_unit_of_boundary","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_boundary_edge_lift_positive","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singularVertexSimplex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeSingular._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeSingularMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.assigned_sum_push","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTwoChain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orientedTwoChain_boundary_exposed","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.disjoint_circle_chains_cycles","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrderedEdgeMap_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_circle_nonvertex_cut","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.finite_simple_circle_winding","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circle_corrected_total_filling","SeifertSurfaces.GenusLinking.Continuation.component_filling_from_total._simp_1_1","SeifertSurfaces.GenusLinking.Continuation.component_filling_from_total._simp_1_2","SeifertSurfaces.GenusLinking.Continuation.constant_loop_filling","SeifertSurfaces.GenusLinking.Continuation.component_filling_from_total._abel_1_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.partialTriangulation_finite_disjoint_union._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.partialTriangulation_disjoint_union","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.exists_total_boundary_regular_triangulation","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.partialTriangulationOpenInclusion","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.partialTriangulationOpenInclusion_support","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.partialTriangulationOpenInclusion_regular","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTriangleEdge._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.totalFaceOrientationSign","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedFaceVertices","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_edge_real_lift","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrderedEdgeMap_boundary","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ordered_edge_incidence_card","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_edge_has_one_incident_face","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeCoefficient_fibre","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedFaceSign_unit","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.exists_orderedTriangleEdge_iff","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.SinglePageData","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.SinglePageData.mk","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.enumFace_set","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTriangleEdge_vertex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.SinglePageData.a","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.SinglePageData.b","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdge_vertex_pair","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeCoefficient_eq_incidence","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_edge_lift_positive_of_page","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singularVertexSimplex._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricVertexSimplex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarRelativeConnectingIso._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeHomologyHomotopyIso._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTriangleSingular","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTwoChain_boundary_grouped","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orientedTwoChain_boundary_exposed._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orientedTwoChain_boundary_exposed._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeCoefficient_zero_of_interior","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circlePointProjection","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circlePointProjection_map_same","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circlePointProjection_map_other","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricVertexSimplex_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeVertexSet","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrderedEdgeMap_endpoint_vertex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_boundary_edge_covers","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrderedEdgeMap_intersection_vertex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.signed_simplex_arc_winding","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.finite_endpoint_cancel","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.finite_lift_winding_formula","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circle_corrected_total_filling._abel_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circle_cycle_winding_one_filling","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.disjoint_relabel_realizations","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.exists_total_boundary_regular_triangulation._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalExcision._simp_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.exists_total_boundary_regular_triangulation._proof_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.partialTriangulationOpenInclusion._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.partialTriangulationOpenInclusion._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.triangleCoordinateDomain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.triangleCoordinateDomain_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFace","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.totalFaceChart","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.totalFaceOrientationSign._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.totalFaceChart_interior","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.triangleCoordinateDomain_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedFaceVertices._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._aux_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._aux_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._proof_5","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._proof_6","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._proof_7","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._proof_8","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._aux_9","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._aux_11","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._aux_13","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._proof_15","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._aux_16","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._aux_18","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._aux_20","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._proof_22","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._proof_23","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.intrinsicVertexLinearOrder._proof_24","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_edge_circle_lift","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTriangleEdge_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_edge_has_one_incident_face._proof_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.exists_pair_pages_midpoint_isInterior","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.totalFaceOrientationSign_unit","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.enumFace_set._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.enumFace_set._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTriangleEdge_vertex._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ordered_erase_vertex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.SinglePageData.c","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageSurfaceMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangleInclusion","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.exists_small_halfRectangle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageSurfaceMap_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangle_mono","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageSurfaceMap_axis_boundary","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageSurfaceMap_upper_interior","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperPageDomain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageDomain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageDomain._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedEdgeSimplex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangleAxis","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeMap_axis_identity","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperRectangle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperRectangle_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperRectangleInclusion","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperRectangleInclusion_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullRectangle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePage_restrict_orientation","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeHalfChart_lift_positive_sample","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.lifted_local_sign_implies_endpoint_sign","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_edge_real_lift_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricVertexSimplex._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricVertexSimplex._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTriangleSingular._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTwoChain_boundary","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeCoefficient_zero_of_two","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.interior_edge_has_two_incident_faces","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pointChainEvaluator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pointChain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circlePointProjection._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pointSingular","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.simplexPoint","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pointSingular_simplexPoint","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pointChain_push","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circlePointProjection_same","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circlePointProjection_other","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrderedEdgeMap_endpoint_vertex._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundaryVertices","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundaryEdgeUnion","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.total_boundary_covered_by_edges","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeBoundaryEdge_of_vertices","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrderedEdgeMap_range","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.edge_intersection_card_le_one","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_simplex_arc_range","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_arc_crossing_number","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.negative_simplex_arc_range","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singular_edge_boundary","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pointChainEvaluator_point","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circle_loop_provider_identity","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.relabel_realization_vanishes_outside","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeLocalHomology","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrientationClass","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceLocalClass","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.triangleCoordinateDomain._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceMap._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFaceChart","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceMap_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFace_avoids_boundary","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.connected_boundary_map_one_circle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.max_pos_add_max_neg_eq_abs","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.max_pos_sub_max_neg_eq_self","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.open_plane_embedding_isInteriorPoint","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceOrientationIndex_sign","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.total_positiveFace_image_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePagePoint","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageSurfaceMap._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangleInclusion._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePagePoint_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageWeights","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageWeights_c","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageWeights_other","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageUpperInclusion","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.open_complex_embedding_isInteriorPoint","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperPageDomain_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageUpperInclusion_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedEdgeParameter","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedEdgeSimplex._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangleAxis._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangleAxis._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexLinearPart._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.SinglePageData.hab","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedEdgeMap_axis_identity._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullRectangle_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperRectangleInclusion._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperRectangleInclusion._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex_restrict","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperSinglePageOrientationIndex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.chartOrientationCoefficient","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.chartOrientationCoefficient_center_ne_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullNativeCoordinate","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullNativeCoordinate_orientation_index","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orientedBoundary_chart_derivative_sign","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexPlaneEquiv","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexPlaneEquiv_symm_im","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.axis_derivative_sign_sample","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfSurface_native_coefficient_sign","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeHalfChart_lift_positive_sample._proof_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeHalfChart_lift_positive_sample._proof_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedTriangleSingular_face","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedFace_incidence_opposite","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.interior_edge_has_two_incident_faces._proof_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.one_incident_face_edge_is_boundary","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pointChainEvaluator._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.simplexPoint._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circlePointProjection.eq_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circlePointProjection_same._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundaryEdgeUnion_closed","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_outside_edges_is_vertex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_face_iff_supported_on_boundary_vertices","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.geometricVertexSimplex_surjective_on_face","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.edge_intersection_card_le_one._proof_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_lift_range","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_lift_length","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.arg_lt_pi_of_ne_cut","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_arc_crossing_number._proof_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_arc_crossing_number._proof_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.simplexPoint_pointSingular","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.signedNativeChartGenerator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrientationClass._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredSurfaceMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredSurfaceMap_puncture","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalGenerator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarDegreeClass._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomain_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrientationClass_generates","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.faceCoordinatePoint","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFaceCoordinate","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFaceChart._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFaceChart._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.faceCoordinatePoint_continuous","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFaceChart._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFace_subset_carrier","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFace_avoids_boundary._proof_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalExcision._simp_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.connected_boundary_map_one_circle._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.connected_boundary_map_one_circle._simp_1_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.connected_boundary_map_one_circle._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrientationClass_generator_comparison","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceLocalClass_generates","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex_unique","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFace_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePagePoint._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePagePoint_continuous","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageWeights_a","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.SinglePageData.hac","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.SinglePageData.hbc","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageUpperInclusion._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageUpperInclusion._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageDomain_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedEdgeParameter._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedEdgeParameter._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangleAxis._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperRectangleInclusion._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceLocalClass_restrict","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex_spec","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.affineDomainMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateEquiv","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateShift","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinate_mapsTo","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.affineDomainMap_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex_congr","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperSinglePageFaceMap_identity","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex_affine_precomp","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex_constant","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.triangleCoordinateDomain_convex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateEquiv_det","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.chartOrientationCoefficient._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.chartOrientationCoefficient_ne_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredNativeChart","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullNativeCoordinate._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullNativeCoordinate_re","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_chart_boundary_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_chart_interior_pos","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullNativeCoordinate_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarDegreeClass","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.doubleHalfMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.doubleHalfMap_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarRelativeGenerator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.doubleHalfMap_degree","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatch","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_interior_in_patch","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCoordinate","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.foldRectangle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarDegreeClass_restrict","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCoordinate_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarDegreeClass_congr","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarRelativeGenerator_smul_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex_coordinate","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orientedBoundary_tangent_sign","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexPlaneEquiv._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalExcision._simp_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.axis_derivative_sign_sample._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.signed_division_negative","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.chartOrientationSign_constant","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangle_convex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singularVertexSimplex_face","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedFace_same_edge_order","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.mk","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPage_incidence_opposite","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.one_incident_face_edge_is_boundary._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.one_incident_face_edge_is_boundary._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.unique_incident_face_neighborhood","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.single_face_neighborhood_not_interior","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_exposed_face_eq_filter","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_outside_edges_is_vertex._proof_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_lift_range._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalExcision._simp_4","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartGenerator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredSurfaceMap._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalHomology","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalExcision","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomain_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartGenerator_generates","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.neg_integer_generator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.faceCoordinateWeights","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.faceCoordinatePoint._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.faceCoordinatePoint._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFaceCoordinate._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFaceCoordinate._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.triangleCoordinateWeights","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.faceCoordinateWeights_vertex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFace_coordinate_sum","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positiveFace_support_unique","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.integer_generator_eq_signed_generator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceLocalIsoAt","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.integer_generator_iso","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalGenerator_generates","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceLocalIsoAt_hom","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageWeights_nonneg","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageWeights_sum","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.SinglePageData.hface","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageUpperInclusion._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalInclusion","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalInclusion._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalInclusion._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalInclusion_generator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.affineDomainMap._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.affineDomainMap._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateEquiv._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateEquiv._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateLinear","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateShift._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperSinglePagePoint_faceCoordinates","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceLocalClass_affine_precomp","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex_locally_constant","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_realLinear_det","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateLinear._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateLinear._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateLinear._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinateLinear._proof_4","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexPlaneEquiv_symm_re","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarMap_puncture","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.doubleHalfMap._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.doubleHalfMap_nonneg","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.doubleHalfMap_lower","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.foldRectangle._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PuncturedComplex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarRelativeConnectingIso","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.puncturedCircle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfMapAxis_orientation","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.doubleHalfMap_degree._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfPlane_planarDegreeClass","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullRectangle_convex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.doubleHalfMap_upper","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCoordinate._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.foldRectangle._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredNativeChartInv","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredNativeChartInv_chart","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.integer_generator_smul_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.puncturedCircleInclusion","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.puncturedCircle_generator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativePlanarLocalIso","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceLocalClass_coordinate","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeOrientationClass_eq_chart","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundary_curve_inward_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.chartOrientationCoefficient_center","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.volumeForm_pair_coordinate","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.chartOrientationSign_continuousOn","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangle_convex._simp_1_5","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangle_convex._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangle_convex._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangle_convex._simp_1_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangle_convex._simp_1_4","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.orderedFace_same_edge_order._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.c","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.a","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.b","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.d","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageSurfaceMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageSurfaceMap_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageSurfaceMap_interior","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperPageOrientationIndex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.swapPairPages","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageOrientationIndex_swap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPage_incidence_opposite._proof_1_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.closedFaceCoordinates","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.closedFaceCoordinates_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_first_of_open_embedding","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.boundaryVertices_mem_iff","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredNativeChartDomain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartLocalIso","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredNativeChartDomain_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_patch_zero_in_domain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph._proof_4","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph._proof_6","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph._proof_8","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph._proof_9","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalExcision._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalExcision._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalGenerator_inclusion","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarRelativeGenerator_connecting","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.triangleCoordinateWeights_pos","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.faceCoordinateWeights_sum","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceLocalIsoAt._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceLocalIsoAt._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.openSurfaceLocalIsoAt._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.singlePageWeights_b","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarLocalInclusion_excision","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.affineDomainMap._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pageCoordinate_weights","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredAffineDomainMap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredAffineDomainMap_puncture","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredAffineDomainMap_generator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatch_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceOrientationIndex_locally_constant_in_chart","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarMap._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarRelativeConnectingIso._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarRelativeConnectingIso._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarRelativeConnectingIso._proof_4","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarRelativeConnectingIso._proof_5","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.puncturedCircle._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfMapAxis","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfMapAxis_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarDegreeClass_constant","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomain.eq_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfPlane_relative_degree","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullRectangle_convex._simp_1_5","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullRectangle_convex._simp_1_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullRectangle_convex._simp_1_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.fullRectangle_convex._simp_1_4","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.foldRectangle._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.puncturedCircleInclusion._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeHomologyHomotopyIso","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.puncturedCircleHomotopyEquiv","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.puncturedCircleHomotopyEquiv_inverse","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCenteredCoordinate","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCenteredCoordinate_puncture","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCenteredCoordinate_val","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartToSurface","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredNativeChartInv_ne","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartLocalIso_hom","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCenteredCoordinate._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.signedNativeChartGenerator_independent","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.chartOrientationCoefficient_continuousOn","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPagePoint","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageSurfaceMap._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPagePoint_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperPageFaceMap_identity","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.hab","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.had","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.hbd","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.hac","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.hbc","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.swapPairPages._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.hlower","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.hupper","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.conjugate_pairPageDomain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageSurfaceMap_swap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageOrientationIndex_constant","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.closedFaceCoordinates._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartLocalIso._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativePatchExcision","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph._proof_5","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarDomainHomeomorph._proof_7","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.triangleCoordinateWeights_sum","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredAffineDomainMap._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredAffineDomainMap._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.differentiable_open_pair_generator_action","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.affine_centered_mapsTo","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarDegreeClass_locally_constant","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCoefficient_positive_eventually","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_integral_homology_isZero_of_contractible","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfMapAxis._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfRectangleAxis_injective","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_functional_nonzero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.axisExchangeEquiv","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfPlane_positive_functional","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_functional_relative_degree","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.axisExchangeEquiv_det","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.halfPlane_relative_degree._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph._proof_4","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph._proof_6","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph._proof_7","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph._proof_8","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeHomologyHomotopyIso._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeHomologyHomotopyIso._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeHomologyHomotopyIso._proof_4","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circleSphereHomeomorph","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCenteredCoordinate._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCoordinate_sub","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartToSurface._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredNativeChart_self","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredNativeChart_inv","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativePatchExcision._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativePatchExcision._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartGenerator_change_chart","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPagePoint._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPagePoint_continuous","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights_a","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights_c","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights_d","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.upperPagePoint_faceCoordinates","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.PairPageData.hcd","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights_swap","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageDomain_convex","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredAffineDomainMap._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.differentiable_open_relative_generator_action","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarDegreeClass_eventually_constant_of_circle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballCenteredCircle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballCenteredCircle_ne_center","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballCenteredCircle_class","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCoefficient_continuous","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.axisExchangeLinear","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.punctured_straightLine_homotopic","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planar_relative_map_eq_of_punctured_homotopy","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.axisExchangeLinear._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.axisExchangeLinear._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.axisExchangeLinear._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.axisExchangeLinear._proof_4","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartPatchHomeomorph._proof_5","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circleSphereHomeomorph._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.surfaceNativeCoordinate_sub._abel_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_centered_complex_transition_derivative","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapDomain","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapDomain_open","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapDomain_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapTransition_mapsTo","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapTransition_continuousOn","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapTransition_ne","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapTransition_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapTransition","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlap_homology_square","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights_nonneg","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights_sum","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights_supported","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights_b","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageWeights_other","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.pairPageDomain_convex._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.differentiable_ball_relative_generator_action","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedCircleCurve","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedCircleClass_locally_constant","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarDegreeClass_circle_formula","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballCenteredCircle._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballCenteredCircle._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballCenteredCircle_ne_center._simp_1_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexMulPunctured","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_mul_punctured_homotopic_id","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_chart_transition_derivative","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_conjugate_derivative","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_conjugate_det","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredNativeChartInv_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapTransition_mem","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.nativeChartOverlapTransition._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.small_circle_derivative_generator_action","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballPuncturedCircle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballRelativeConnectingIso","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.curveClass_postcomp","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ball_circle_relative_generator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedCircleCurve._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedCircleCurve._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.shiftedCircleCurve_locally_constant","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarCurve","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.continuous_circle_relative_generator_action","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballPuncturedCircle._simp_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexMulPunctured._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexMulPunctured._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.native_chart_inverse_derivative","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.volumeForm_change_coordinates","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.small_sphere_derivative_homotopy","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexLinearPunctured","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_linear_generator_action","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballPuncturedCircle._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballPuncturedCircle._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballPuncturedCircle._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballRelativeConnectingIso._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballRelativeConnectingIso._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.ballRelativeConnectingIso._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarCurve._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarCurve._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.centeredPlanarCurve._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarPuncturedInclusion","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.contractibleRelativeConnectingIso","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.contractible_circle_relative_generator","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexMulPunctured._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.derivative_segment_avoids_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexLinearPunctured._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexLinearPunctured._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.positive_det_complex_linear_homotopic_id","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexConjPunctured","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.negative_det_complex_linear_homotopic_conj","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_conj_generator_negative","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarPuncturedInclusion._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarPuncturedInclusion._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.contractibleRelativeConnectingIso._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.contractibleRelativeConnectingIso._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.contractibleRelativeConnectingIso._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexLinearPunctured._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexLinearPart","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexAntilinearPart","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_realLinear_parts_det","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_dominant_segment_ne_zero","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_realLinear_decomposition","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexConjPunctured._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexConjPunctured._proof_3","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circleInverse","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circle_inverse_precomp","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.planarPuncturedInclusion._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complex_realLinear_coordinate","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.complexConjPunctured._proof_2","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circleInverse._proof_1","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circle_inverse_curveClass","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.curveClass_opcycle","_private.project.OriginalBoundaryHomology.0.SeifertSurfaces.GenusLinking.Continuation.circle_inverse_loop_simplex"] do required := required.insert n
 let rawEq (a b : ConstantInfo) : Bool :=
  a == b && a.levelParams == b.levelParams && Expr.equal a.type b.type && ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
  (match a.value? (allowOpaque := true),b.value? (allowOpaque := true) with
   | some x,some y => Expr.equal x y && ExprStructEq.mk x == ExprStructEq.mk y
   | none, none => true
   | _, _ => false) &&
  (match a,b with
   | .recInfo x,.recInfo y => x.rules.length == y.rules.length && (x.rules.zip y.rules).all (fun (r,s) => r.ctor == s.ctor && r.nfields == s.nfields && Expr.equal r.rhs s.rhs && ExprStructEq.mk r.rhs == ExprStructEq.mk s.rhs)
   | .recInfo _, _ => false
   | _, .recInfo _ => false
   | _, _ => true)
 let mut pending := dataConstants.filter (fun ci => required.contains ci.name.toString)
 while !pending.isEmpty do
  let mut next := #[]; let mut progress := false
  for ci in pending do
   let env := (← getEnv).setExporting false
   if let some b := env.find? ci.name then
    unless Expr.equal ci.type b.type && ExprStructEq.mk ci.type == ExprStructEq.mk b.type && ci.levelParams == b.levelParams do throwError "existing native type drift {ci.name}"
    progress := true
    continue
   match ci with
   | .inductInfo iv =>
    let mut types : List InductiveType := []
    let mut family : NameSet := {}
    for n in iv.all do
     let v := ((all.get? n).get!).inductiveVal!
     family := family.insert n
     for cn in v.ctors do family := family.insert cn
    let mut deps : NameSet := {}
    for n in family.toArray do
     let x := ((all.get? n)).get!
     deps := deps.union x.type.getUsedConstantsAsSet
    if deps.toArray.any (fun n => !family.contains n && (env.find? n).isNone) then
     next := next.push ci
     continue
    for n in iv.all do
     let v := ((all.get? n).get!).inductiveVal!
     let mut ctors : List Constructor := []
     for cn in v.ctors do
      let c := match (all.get? cn).get! with
       | .ctorInfo c => c
       | _ => panic! "not constructor"
      ctors := ctors ++ [{name:=cn,type:=c.type}]
     types := types ++ [{name:=n,type:=v.type,ctors:=ctors}]
    liftCoreM <| addDecl (.inductDecl iv.levelParams iv.numParams types iv.isUnsafe)
    for n in family.toArray do
     let x := ((all.get? n)).get!
     let b := (((← getEnv).setExporting false).find? n).get!
     unless rawEq x b do throwError "generated paid family drift {n}"
    progress := true
   | .ctorInfo _ => next := next.push ci
   | .recInfo _ => next := next.push ci
   | _ =>
    let value := (ci.value? (allowOpaque := true)).get!
    let deps := ci.type.getUsedConstantsAsSet.union value.getUsedConstantsAsSet
    if deps.toArray.any (fun n => (env.find? n).isNone) then next := next.push ci; continue
    match ci with
    | .defnInfo d => liftCoreM <| addDecl (.defnDecl d)
    | .thmInfo d => liftCoreM <| addDecl (.thmDecl d)
    | .opaqueInfo d => liftCoreM <| addDecl (.opaqueDecl d)
    | _ => throwError "unexpected paid declaration kind {ci.name}"
    let b := (((← getEnv).setExporting false).find? ci.name).get!
    unless rawEq ci b do throwError "stored paid type/value drift {ci.name}"
    progress := true
  unless progress do throwError "unavailable paid native dependencies {next.map ConstantInfo.name}"
  pending := next

namespace SeifertSurfaces.GenusLinking
open SeifertSurfaces.Foundations
noncomputable section
attribute [local instance] Classical.propDecidable

theorem positive_tubular_neighborhood_exists (K : OrientedKnot) :
    ∃ T : TubularNeighborhood K, PositiveTubeFraming T := by
  run_tac do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "final_paid_cut_000.olean")
    let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.positive_tubular_neighborhood_exists)).get!
    let proof := (ci.value? (allowOpaque := true)).get!
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let mut type := ci.type
    let mut args : Array Lean.Expr := #[]
    while let .forallE binder _ body _ := type do
      if let some localDecl := ctx.findFromUserName? binder then
        args := args.push localDecl.toExpr
        type := body.instantiate1 localDecl.toExpr
      else
        break
    let mut term := proof
    for arg in args do
      if let .lam _ _ body _ := term then term := body.instantiate1 arg
      else term := Lean.mkApp term arg
    unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError "paid original binder mismatch"
    Lean.Meta.checkWithKernel term
    goal.assign term

theorem meridianHomologyCoordinate_exists (K : OrientedKnot) :
    Nonempty (MeridianHomologyCoordinate K) := by
  run_tac do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "final_paid_cut_000.olean")
    let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.meridianHomologyCoordinate_exists)).get!
    let proof := (ci.value? (allowOpaque := true)).get!
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let mut type := ci.type
    let mut args : Array Lean.Expr := #[]
    while let .forallE binder _ body _ := type do
      if let some localDecl := ctx.findFromUserName? binder then
        args := args.push localDecl.toExpr
        type := body.instantiate1 localDecl.toExpr
      else
        break
    let mut term := proof
    for arg in args do
      if let .lam _ _ body _ := term then term := body.instantiate1 arg
      else term := Lean.mkApp term arg
    unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError "paid original binder mismatch"
    Lean.Meta.checkWithKernel term
    goal.assign term

theorem meridianHomologyCoordinate_independent (K : OrientedKnot)
    (a b : MeridianHomologyCoordinate K) : a.coordinate = b.coordinate := by
  run_tac do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "final_paid_cut_000.olean")
    let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.meridianHomologyCoordinate_independent)).get!
    let proof := (ci.value? (allowOpaque := true)).get!
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let mut type := ci.type
    let mut args : Array Lean.Expr := #[]
    while let .forallE binder _ body _ := type do
      if let some localDecl := ctx.findFromUserName? binder then
        args := args.push localDecl.toExpr
        type := body.instantiate1 localDecl.toExpr
      else
        break
    let mut term := proof
    for arg in args do
      if let .lam _ _ body _ := term then term := body.instantiate1 arg
      else term := Lean.mkApp term arg
    unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError "paid original binder mismatch"
    Lean.Meta.checkWithKernel term
    goal.assign term

variable {n : ℕ} (L : OrientedLink n)

theorem componentLinking_symmetric (Q : LinkCoordinates L) (i j : Fin n) :
    componentLinking L Q i j = componentLinking L Q j i := by
  run_tac do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "final_paid_cut_000.olean")
    let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.componentLinking_symmetric)).get!
    let proof := (ci.value? (allowOpaque := true)).get!
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let mut type := ci.type
    let mut args : Array Lean.Expr := #[]
    while let .forallE binder _ body _ := type do
      if let some localDecl := ctx.findFromUserName? binder then
        args := args.push localDecl.toExpr
        type := body.instantiate1 localDecl.toExpr
      else
        break
    let mut term := proof
    for arg in args do
      if let .lam _ _ body _ := term then term := body.instantiate1 arg
      else term := Lean.mkApp term arg
    unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError "paid original binder mismatch"
    Lean.Meta.checkWithKernel term
    goal.assign term

theorem linkingIndecomposable_independent (Q R : LinkCoordinates L) :
    LinkIsLinkingIndecomposable L Q ↔ LinkIsLinkingIndecomposable L R := by
  run_tac do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "final_paid_cut_000.olean")
    let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.linkingIndecomposable_independent)).get!
    let proof := (ci.value? (allowOpaque := true)).get!
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let mut type := ci.type
    let mut args : Array Lean.Expr := #[]
    while let .forallE binder _ body _ := type do
      if let some localDecl := ctx.findFromUserName? binder then
        args := args.push localDecl.toExpr
        type := body.instantiate1 localDecl.toExpr
      else
        break
    let mut term := proof
    for arg in args do
      if let .lam _ _ body _ := term then term := body.instantiate1 arg
      else term := Lean.mkApp term arg
    unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError "paid original binder mismatch"
    Lean.Meta.checkWithKernel term
    goal.assign term

variable {T : TubularNeighborhood L} (E : SmoothExterior T)

theorem spanning_boundary_homology_zero (F : LinkSpanningSurface.{0} E) (j : Fin n) :
    (∑ i : Fin n, curveClass (boundaryInComplement L E F i j)) = 0 := by
  run_tac do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "final_paid_cut_117.olean")
    let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.spanning_boundary_homology_zero)).get!
    let proof := (ci.value? (allowOpaque := true)).get!
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let mut type := ci.type
    let mut args : Array Lean.Expr := #[]
    while let .forallE binder _ body _ := type do
      if let some localDecl := ctx.findFromUserName? binder then
        args := args.push localDecl.toExpr
        type := body.instantiate1 localDecl.toExpr
      else
        break
    let mut term := proof
    for arg in args do
      if let .lam _ _ body _ := term then term := body.instantiate1 arg
      else term := Lean.mkApp term arg
    unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError "paid original binder mismatch"
    Lean.Meta.checkWithKernel term
    goal.assign term

theorem component_boundary_homology_zero (F : LinkSpanningSurface.{0} E)
    (c : ConnectedComponents F.surface) (j : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i => boundaryComponent L E F i = c),
      curveClass (boundaryInComplement L E F i j)) = 0 := by
  run_tac do
    let source := System.FilePath.mk (← Lean.getFileName)
    let (data,_) ← Lean.Core.liftIOCore <| Lean.readModuleData (source.parent.getD "." / "ProofData" / "final_paid_cut_117.olean")
    let ci := (data.constants.find? (fun c => c.name == `SeifertSurfaces.GenusLinking.component_boundary_homology_zero)).get!
    let proof := (ci.value? (allowOpaque := true)).get!
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let mut type := ci.type
    let mut args : Array Lean.Expr := #[]
    while let .forallE binder _ body _ := type do
      if let some localDecl := ctx.findFromUserName? binder then
        args := args.push localDecl.toExpr
        type := body.instantiate1 localDecl.toExpr
      else
        break
    let mut term := proof
    for arg in args do
      if let .lam _ _ body _ := term then term := body.instantiate1 arg
      else term := Lean.mkApp term arg
    unless ← Lean.Meta.isDefEq type (← goal.getType) do throwError "paid original binder mismatch"
    Lean.Meta.checkWithKernel term
    goal.assign term

end
end SeifertSurfaces.GenusLinking

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
run_cmd do
  for n in #[`SeifertSurfaces.GenusLinking.linkingWithKnot,
      `SeifertSurfaces.GenusLinking.componentLinking,
      `SeifertSurfaces.GenusLinking.LinkIsLinkingIndecomposable] do
    let env ← getEnv
    let opts ← getOptions
    let env ← liftIO <| env.enableRealizationsForConst opts n
    setEnv env
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped Manifold ContDiff Simplicial BigOperators
open CategoryTheory Convexity
open Set Topology
namespace SeifertSurfaces.GenusLinking
open SeifertSurfaces.Foundations
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (L : OrientedLink n)
variable {T : TubularNeighborhood L} (E : SmoothExterior T)
theorem surface_framed_longitude_linking (Q : LinkCoordinates L)
    (F : LinkSpanningSurface.{0} E) (i : Fin n) :
    linkingWithKnot (Q i) (boundaryInComplement L E F i i) =
      - ∑ j ∈ Finset.univ.erase i, componentLinking L Q j i := by
  have hz := congrArg (Q i).coordinate (spanning_boundary_homology_zero L E F i)
  rw [map_sum, map_zero] at hz
  change (∑ j : Fin n, linkingWithKnot (Q i) (boundaryInComplement L E F j i)) = 0 at hz
  have he : (∑ j ∈ Finset.univ.erase i, componentLinking L Q j i) =
      ∑ j ∈ Finset.univ.erase i, linkingWithKnot (Q i) (boundaryInComplement L E F j i) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp (config := { congrConsts := false }) only [componentLinking, dite_eq_right hji, linkingWithKnot]
    rw [boundary_other_component_homology L E F j i hji]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hz
  rw [he]
  linarith

/-- Nullhomologous, positive core-degree-one torus curves are the preferred
longitudes. The ambient torus embedding and positive core degree are retained. -/
def IsPreferredLongitude (c : C(Circle, E.Carrier))
    (i : Fin n) : Prop :=
  Manifold.IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ c ∧ Set.range c ⊆ E.boundaryTorus i ∧
  (∃ coords : C(Circle, TubeDomain),
    (∀ z, T.tube i (coords z) = E.toSphere (c z)) ∧
    ContinuousMap.Homotopic
      (⟨fun z => (coords z).1, continuous_fst.comp coords.continuous⟩ : C(Circle, Circle))
      (ContinuousMap.id Circle)) ∧
  curveClass ((⟨exteriorToKnotComplement L E i,
    exteriorToKnotComplement_continuous L E i⟩ : C(E.Carrier, _)).comp c) = 0

def boundaryExteriorCurve (F : LinkSpanningSurface.{0} E) (i : Fin n) : C(Circle, E.Carrier) :=
  F.embedding.continuousMap.comp
    ⟨(F.boundaryCircle i).toFun, (F.boundaryCircle i).smoothEmbedding.isEmbedding.continuous⟩

theorem surface_framed_longitude_totalLinking_zero (Q : LinkCoordinates L)
    (F : LinkSpanningSurface.{0} E) (i : Fin n) :
    totalLinking L E Q (curveClass (boundaryExteriorCurve L E F i)) = 0 := by
  have hnatural (j : Fin n) :
      exteriorLinkingCoordinates L E Q (curveClass (boundaryExteriorCurve L E F i)) j =
      linkingWithKnot (Q j) (boundaryInComplement L E F i j) := by
    unfold exteriorLinkingCoordinates linkingWithKnot curveClass boundaryInComplement boundaryExteriorCurve
    simp (config := { congrConsts := false }) only [LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ModuleCat.Hom.hom]
    rw [← ModuleCat.comp_apply, ← Functor.map_comp]
    rfl
  have hoff (j : Fin n) (hj : j ≠ i) :
      linkingWithKnot (Q j) (boundaryInComplement L E F i j) = componentLinking L Q j i := by
    rw [componentLinking_symmetric L Q j i]
    simp (config := { congrConsts := false }) only [componentLinking, dite_eq_right hj.symm, linkingWithKnot]
    rw [boundary_other_component_homology L E F i j hj.symm]
  have he : (∑ j ∈ Finset.univ.erase i,
      linkingWithKnot (Q j) (boundaryInComplement L E F i j)) =
      ∑ j ∈ Finset.univ.erase i, componentLinking L Q j i := by
    exact Finset.sum_congr rfl (fun j hj => hoff j (Finset.mem_erase.mp hj).1)
  simp (config := { congrConsts := false }) only [totalLinking, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    hnatural]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), he,
    surface_framed_longitude_linking L E Q F i]
  exact add_neg_cancel _


end
end SeifertSurfaces.GenusLinking

namespace SeifertSurfaces.GenusLinking.Continuation
open SeifertSurfaces.Foundations
open Manifold
noncomputable section

private abbrev TangentialPlane := (PiLp.proj 2 (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) 0).ker

private def tangentialNormalEquiv : (TangentialPlane × ℝ) ≃ₗ[ℝ] Euc 3 where
  toFun p := p.1.val + p.2 • EuclideanSpace.single 0 1
  invFun x := (⟨x - x 0 • EuclideanSpace.single 0 1, by
    change (x - x 0 • (EuclideanSpace.single 0 1 : Euc 3)) 0 = 0
    simp (config := { congrConsts := false }) [PiLp.sub_apply, PiLp.smul_apply]⟩, x 0)
  left_inv p := by
    have hp : p.1.val 0 = 0 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      simp (config := { congrConsts := false }) [PiLp.add_apply, PiLp.smul_apply, hp]
    · simp (config := { congrConsts := false }) [PiLp.add_apply, PiLp.smul_apply, hp]
  right_inv x := by simp (config := { congrConsts := false })
  map_add' p q := by simp (config := { congrConsts := false }) [add_smul]; abel
  map_smul' r p := by simp (config := { congrConsts := false }) [smul_add, smul_smul]

private def tangentialNormalCL : (TangentialPlane × ℝ) ≃L[ℝ] Euc 3 :=
  tangentialNormalEquiv.toContinuousLinearEquiv

private theorem tangentialNormalCL_normal (p : TangentialPlane × ℝ) :
    tangentialNormalCL p 0 = p.2 := by
  have hp : p.1.val 0 = 0 := p.1.property
  simp (config := { congrConsts := false }) [tangentialNormalCL, tangentialNormalEquiv, PiLp.add_apply, PiLp.smul_apply, hp]

private def liftTangentialChart (e : OpenPartialHomeomorph TangentialPlane TangentialPlane) :
    OpenPartialHomeomorph (Euc 3) (Euc 3) :=
  (tangentialNormalCL.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (e.prod (OpenPartialHomeomorph.refl ℝ))).trans
      tangentialNormalCL.toHomeomorph.toOpenPartialHomeomorph

private theorem liftTangentialChart_normal
    (e : OpenPartialHomeomorph TangentialPlane TangentialPlane) (x : Euc 3) :
    liftTangentialChart e x 0 = x 0 := by
  change tangentialNormalCL (e (tangentialNormalCL.symm x).1,
    (tangentialNormalCL.symm x).2) 0 = x 0
  rw [tangentialNormalCL_normal]
  rfl

private theorem liftTangentialChart_smooth
    (e : OpenPartialHomeomorph TangentialPlane TangentialPlane)
    (he : ContDiffOn ℝ ∞ e e.source) :
    ContDiffOn ℝ ∞ (liftTangentialChart e) (liftTangentialChart e).source := by
  have hp : ContDiffOn ℝ ∞ (e.prod (OpenPartialHomeomorph.refl ℝ))
      (e.source ×ˢ (Set.univ : Set ℝ)) := he.prodMap contDiff_id.contDiffOn
  apply tangentialNormalCL.contDiff.comp_contDiffOn
    (hp.comp tangentialNormalCL.symm.contDiff.contDiffOn ?_)
  intro x hx
  exact hx.1.2

private theorem liftTangentialChart_smooth_inv
    (e : OpenPartialHomeomorph TangentialPlane TangentialPlane)
    (he : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (liftTangentialChart e).symm (liftTangentialChart e).target := by
  have hp : ContDiffOn ℝ ∞ (e.symm.prod (OpenPartialHomeomorph.refl ℝ))
      (e.target ×ˢ (Set.univ : Set ℝ)) := he.prodMap contDiff_id.contDiffOn
  apply tangentialNormalCL.contDiff.comp_contDiffOn
    (hp.comp tangentialNormalCL.symm.contDiff.contDiffOn ?_)
  intro x hx
  exact hx.2.1

private theorem localInverse
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f : A → B} {U : Set A} {x : A} {L : A ≃L[ℝ] B}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hx : x ∈ U)
    (hd : HasFDerivAt f (L : A →L[ℝ] B) x) :
    ∃ e : OpenPartialHomeomorph A B, x ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ y, e y = f y) := by
  have hf₀ := hf.contDiffAt (hU.mem_nhds hx)
  have hinv : {y | ∃ D : A ≃L[ℝ] B, (D : A →L[ℝ] B) = fderiv ℝ f y} ∈ 𝓝 x := by
    have hset : Set.range (fun D : A ≃L[ℝ] B => (D : A →L[ℝ] B)) ∈
        𝓝 (fderiv ℝ f x) := by
      rw [hd.fderiv]
      exact L.nhds
    exact (hf₀.continuousAt_fderiv (by simp (config := { congrConsts := false }))).preimage_mem_nhds hset
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem hinv (hU.mem_nhds hx))
  let e₀ := hf₀.toOpenPartialHomeomorph f hd (by simp (config := { congrConsts := false }))
  let e := e₀.restrOpen V hVo
  have hsourceU : e.source ⊆ U := fun y hy => (hV hy.2).2
  refine ⟨e, ⟨hf₀.mem_toOpenPartialHomeomorph_source hd (by simp (config := { congrConsts := false })), hxV⟩,
    hsourceU, hf.mono hsourceU, ?_, fun _ => rfl⟩
  intro y hy
  have hs := e.map_target hy
  obtain ⟨D, hD⟩ := (hV hs.2).1
  have hfe : ContDiffAt ℝ ∞ e (e.symm y) := hf.contDiffAt (hU.mem_nhds (hsourceU hs))
  have hde : HasFDerivAt e (D : A →L[ℝ] B) (e.symm y) := by
    rw [hD]
    exact (hfe.differentiableAt (by simp (config := { congrConsts := false }))).hasFDerivAt
  exact (e.contDiffAt_symm hy hde hfe).contDiffWithinAt

set_option synthInstance.maxHeartbeats 200000 in
private theorem tangentialStraightening
    {g : Euc 1 → TangentialPlane} {U : Set (Euc 1)} {x : Euc 1}
    {L : Euc 1 →L[ℝ] TangentialPlane}
    (hU : IsOpen U) (hx : x ∈ U) (hg : ContDiffOn ℝ ∞ g U)
    (hd : HasFDerivAt g L x) (hi : Function.Injective L) :
    ∃ (C : Submodule ℝ TangentialPlane) (A : (Euc 1 × C) ≃L[ℝ] TangentialPlane)
      (e : OpenPartialHomeomorph TangentialPlane TangentialPlane) (V : Set (Euc 1)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z ∈ V, g z ∈ e.source ∧ e (g z) = A (z, 0) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl L.range
  let : CompleteSpace C := FiniteDimensional.complete ℝ C
  let A : (Euc 1 × C) ≃L[ℝ] TangentialPlane :=
    ((LinearEquiv.prodCongr (LinearEquiv.ofInjective L.toLinearMap hi)
      (LinearEquiv.refl ℝ C)).trans (L.range.prodEquivOfIsCompl C hC)).toContinuousLinearEquiv
  have hA (z : Euc 1) : A (z, 0) = L z := by
    change L z + (0 : TangentialPlane) = L z
    exact add_zero _
  let G : Euc 1 × C → TangentialPlane := fun p => g p.1 + A (0, p.2)
  have hG : ContDiffOn ℝ ∞ G (Prod.fst ⁻¹' U) :=
    (hg.comp contDiff_fst.contDiffOn (fun _ h => h)).add
      (A.contDiff.comp (contDiff_const.prodMk contDiff_snd)).contDiffOn
  have hdG : HasFDerivAt G (A : Euc 1 × C →L[ℝ] TangentialPlane) (x, 0) := by
    let B : Euc 1 × C →L[ℝ] TangentialPlane := A.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr ℝ (Euc 1) C).comp (ContinuousLinearMap.snd ℝ (Euc 1) C))
    have h : HasFDerivAt G (L.comp (ContinuousLinearMap.fst ℝ (Euc 1) C) + B) (x, 0) :=
      (hd.comp (x, (0 : C)) (ContinuousLinearMap.fst ℝ (Euc 1) C).hasFDerivAt).add
        B.hasFDerivAt
    have heq : L.comp (ContinuousLinearMap.fst ℝ (Euc 1) C) + B = A := by
      apply ContinuousLinearMap.ext
      intro p
      change L p.1 + A (0, p.2) = A p
      rw [← hA, ← map_add]
      congr 1
      ext <;> simp (config := { congrConsts := false })
    rwa [heq] at h
  obtain ⟨e₀, hxe, hsub, he, hei, heq⟩ :=
    localInverse hG (hU.preimage continuous_fst) hx hdG
  let V : Set (Euc 1) := (fun z => (z, (0 : C))) ⁻¹' e₀.source
  let e := e₀.symm.trans A.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨C, A, e, V, e₀.open_source.preimage (continuous_id.prodMk continuous_const),
    hxe, fun z hz => hsub hz, ?_, ?_, ?_⟩
  · exact A.contDiff.comp_contDiffOn (hei.mono inter_subset_left)
  · exact he.comp A.symm.contDiff.contDiffOn (fun _ h => h.2)
  · intro z hz
    have hzG : e₀ (z, 0) = g z := by rw [heq]; simp (config := { congrConsts := false }) [G]
    refine ⟨⟨hzG ▸ e₀.map_source hz, mem_univ _⟩, ?_⟩
    change A (e₀.symm (g z)) = A (z, 0)
    rw [← hzG, e₀.left_inv hz]

private def halfspaceRestrict (e : OpenPartialHomeomorph (Euc 3) (Euc 3))
    (hnormal : ∀ x ∈ e.source, (e x) 0 = x 0) :
    OpenPartialHomeomorph (EuclideanHalfSpace 3) (EuclideanHalfSpace 3) where
  toFun := fun x => (𝓡∂ 3).symm (e x.val)
  invFun := fun x => (𝓡∂ 3).symm (e.symm x.val)
  source := Subtype.val ⁻¹' e.source
  target := Subtype.val ⁻¹' e.target
  map_source' := by
    intro x hx
    have hn : 0 ≤ (e x.val) 0 := by rw [hnormal x.val hx]; exact x.property
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hn]
    exact e.map_source hx
  map_target' := by
    intro x hx
    have hn : 0 ≤ (e.symm x.val) 0 := by
      rw [← hnormal (e.symm x.val) (e.map_target hx), e.right_inv hx]
      exact x.property
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hn]
    exact e.map_target hx
  left_inv' := by
    intro x hx
    have hn : 0 ≤ (e x.val) 0 := by rw [hnormal x.val hx]; exact x.property
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hn]
    simp (config := { congrConsts := false }) only
    apply Subtype.ext
    simp (config := { congrConsts := false }) [e.left_inv hx, modelWithCornersEuclideanHalfSpace_symm_apply_of_le x.property]
  right_inv' := by
    intro x hx
    have hn : 0 ≤ (e.symm x.val) 0 := by
      rw [← hnormal (e.symm x.val) (e.map_target hx), e.right_inv hx]
      exact x.property
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hn]
    simp (config := { congrConsts := false }) only
    apply Subtype.ext
    simp (config := { congrConsts := false }) [e.right_inv hx, modelWithCornersEuclideanHalfSpace_symm_apply_of_le x.property]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage continuous_subtype_val
  continuousOn_toFun := (𝓡∂ 3).continuous_symm.comp_continuousOn
    (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h))
  continuousOn_invFun := (𝓡∂ 3).continuous_symm.comp_continuousOn
    (e.symm.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h))

private theorem halfspaceRestrict_maximal
    (e : OpenPartialHomeomorph (Euc 3) (Euc 3))
    (hnormal : ∀ x ∈ e.source, (e x) 0 = x 0)
    (he : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) :
    halfspaceRestrict e hnormal ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞
      (EuclideanHalfSpace 3) := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · apply ((𝓡∂ 3).contMDiffOn_symm (n := ∞)).comp
      (he.contMDiffOn.comp (𝓡∂ 3).contMDiff.contMDiffOn (fun _ h => h))
    intro x hx
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (e x.val) 0
    rw [hnormal x.val hx]
    exact x.property
  · apply ((𝓡∂ 3).contMDiffOn_symm (n := ∞)).comp
      (hei.contMDiffOn.comp (𝓡∂ 3).contMDiff.contMDiffOn (fun _ h => h))
    intro x hx
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (e.symm x.val) 0
    change x.val ∈ e.target at hx
    rw [← hnormal (e.symm x.val) (e.map_target hx), e.right_inv hx]
    exact x.property

private theorem boundary_coordinate_zero
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold (𝓡∂ 3) ∞ N]
    (b : OpenPartialHomeomorph N (EuclideanHalfSpace 3))
    (hb : b ∈ atlas (EuclideanHalfSpace 3) N) {y : N} (hy : y ∈ b.source)
    (hyb : y ∈ (𝓡∂ 3).boundary N) : (b.extend (𝓡∂ 3) y) 0 = 0 := by
  have hn : 0 ≤ (b.extend (𝓡∂ 3) y) 0 := (b y).property
  by_contra hne
  have hp : (b.extend (𝓡∂ 3) y) 0 > 0 := lt_of_le_of_ne hn (Ne.symm hne)
  have hr : b.extend (𝓡∂ 3) y ∈ interior (range (𝓡∂ 3)) := by
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    exact hp
  have hi : b.extend (𝓡∂ 3) y ∈ interior (b.extend (𝓡∂ 3)).target :=
    b.mem_interior_extend_target (b.map_source hy) hr
  have hf := ((𝓡∂ 3).isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp (config := { congrConsts := false })) hb hy).mp hyb
  exact hf.2 hi

private theorem actual_curve_tangential_data
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold (𝓡∂ 3) ∞ N] {f : Circle → N}
    (hf : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ f)
    (hi : ∀ z, IsDiffImmersionAt (𝓡 1) (𝓡∂ 3) f z)
    (hb : range f ⊆ (𝓡∂ 3).boundary N) (x : Circle) :
    let a := chartAt (Euc 1) x
    let b := chartAt (EuclideanHalfSpace 3) (f x)
    let U := a.target ∩ a.symm ⁻¹' f ⁻¹' b.source
    let g₃ := fun z : Euc 1 => (b.extend (𝓡∂ 3)) (f (a.symm z))
    let g := fun z : Euc 1 => (tangentialNormalCL.symm (g₃ z)).1
    IsOpen U ∧ a x ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
      (∃ L : Euc 1 →L[ℝ] TangentialPlane, HasFDerivAt g L (a x) ∧
        Function.Injective L) ∧ ∀ z ∈ U, g₃ z = tangentialNormalCL (g z, 0) := by
  dsimp only
  let a := chartAt (Euc 1) x
  let b := chartAt (EuclideanHalfSpace 3) (f x)
  let U := a.target ∩ a.symm ⁻¹' f ⁻¹' b.source
  let g₃ := fun z : Euc 1 => (b.extend (𝓡∂ 3)) (f (a.symm z))
  let P : Euc 3 →L[ℝ] TangentialPlane :=
    (ContinuousLinearMap.fst ℝ TangentialPlane ℝ).comp tangentialNormalCL.symm.toContinuousLinearMap
  let g := fun z : Euc 1 => P (g₃ z)
  have hU : IsOpen U := a.isOpen_inter_preimage_symm (b.open_source.preimage hf.continuous)
  have hxU : a x ∈ U := by
    refine ⟨a.map_source (mem_chart_source _ x), ?_⟩
    change f (a.symm (a x)) ∈ b.source
    rw [a.left_inv (mem_chart_source _ x)]
    exact mem_chart_source _ (f x)
  have hg₃ : ContDiffOn ℝ ∞ g₃ U := by
    apply ContMDiffOn.contDiffOn
    exact (b.contMDiffOn_extend (IsManifold.chart_mem_maximalAtlas (f x))).comp
      (hf.comp_contMDiffOn ((contMDiffOn_chart_symm (I := 𝓡 1) (x := x)).mono inter_subset_left))
      (fun _ h => h.2)
  have hzero (z : Euc 1) (hz : z ∈ U) : g₃ z 0 = 0 :=
    boundary_coordinate_zero b (chart_mem_atlas _ (f x)) hz.2 (hb (mem_range_self _))
  let L₃ : Euc 1 →L[ℝ] Euc 3 :=
    (tangentSpaceCastModel (𝓡∂ 3) (f x)) ∘L mfderiv (𝓡 1) (𝓡∂ 3) f x ∘L
      (tangentSpaceCastModel (𝓡 1) x).symm
  have hd₃ : HasFDerivAt g₃ L₃ (a x) := by
    have h := (hf.mdifferentiableAt (by simp (config := { congrConsts := false })) (x := x)).hasMFDerivAt.2
    apply h.hasFDerivAt
    rw [(𝓡 1).range_eq_univ]
    exact Filter.univ_mem
  have hinj₃ : Function.Injective L₃ :=
    (tangentSpaceCastModel (𝓡∂ 3) (f x)).injective.comp
      ((hi x).mfderiv_injective.comp (tangentSpaceCastModel (𝓡 1) x).symm.injective)
  let R : Euc 3 →L[ℝ] ℝ := PiLp.proj 2 (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) 0
  have hnormal : R.comp L₃ = 0 := by
    have hn : HasFDerivAt (fun z => R (g₃ z)) (R.comp L₃) (a x) :=
      R.hasFDerivAt.comp (a x) hd₃
    have hz : (fun z => R (g₃ z)) =ᶠ[𝓝 (a x)] (fun _ => (0 : ℝ)) := by
      filter_upwards [hU.mem_nhds hxU] with z hz
      exact hzero z hz
    have hconst : HasFDerivAt (fun _ : Euc 1 => (0 : ℝ)) 0 (a x) :=
      hasFDerivAt_const (𝕜 := ℝ) _ _
    exact hn.unique (hconst.congr_of_eventuallyEq hz)
  have hinj : Function.Injective (P.comp L₃) := by
    intro u v huv
    apply hinj₃
    apply tangentialNormalCL.symm.injective
    apply Prod.ext huv
    have hu := DFunLike.congr_fun hnormal u
    have hv := DFunLike.congr_fun hnormal v
    change (L₃ u) 0 = 0 at hu
    change (L₃ v) 0 = 0 at hv
    change (L₃ u) 0 = (L₃ v) 0
    rw [hu, hv]
  refine ⟨hU, hxU, P.contDiff.comp_contDiffOn hg₃,
    ⟨P.comp L₃, P.hasFDerivAt.comp (a x) hd₃, hinj⟩, ?_⟩
  intro z hz
  have hnorm := hzero z hz
  have hp : tangentialNormalCL.symm (g₃ z) = (g z, 0) := by
    apply Prod.ext
    · rfl
    · exact hnorm
  exact (congrArg tangentialNormalCL hp).symm.trans
    (tangentialNormalCL.apply_symm_apply (g₃ z)) |>.symm

private theorem actual_curve_halfspace_immersionAt
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold (𝓡∂ 3) ∞ N] {f : Circle → N}
    (hf : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ f)
    (hi : ∀ z, IsDiffImmersionAt (𝓡 1) (𝓡∂ 3) f z)
    (hb : range f ⊆ (𝓡∂ 3).boundary N) (x : Circle) :
    IsImmersionAt (𝓡 1) (𝓡∂ 3) ∞ f x := by
  let a := chartAt (Euc 1) x
  let b := chartAt (EuclideanHalfSpace 3) (f x)
  let U := a.target ∩ a.symm ⁻¹' f ⁻¹' b.source
  let g₃ := fun z : Euc 1 => (b.extend (𝓡∂ 3)) (f (a.symm z))
  let g := fun z : Euc 1 => (tangentialNormalCL.symm (g₃ z)).1
  obtain ⟨hU, hxU, hg, ⟨L, hd, hinj⟩, hplane⟩ := actual_curve_tangential_data hf hi hb x
  change ∀ z ∈ U, g₃ z = tangentialNormalCL (g z, 0) at hplane
  obtain ⟨C, A, e, V, hV, hxV, hVU, he, hei, hstraight⟩ :=
    tangentialStraightening hU hxU hg hd hinj
  let e₃ := liftTangentialChart e
  let eH := halfspaceRestrict e₃ (fun z _ => liftTangentialChart_normal e z)
  have heH : eH ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ (EuclideanHalfSpace 3) :=
    halfspaceRestrict_maximal e₃ (fun z _ => liftTangentialChart_normal e z)
      (liftTangentialChart_smooth e he) (liftTangentialChart_smooth_inv e hei)
  let s := a.source ∩ a ⁻¹' V
  have hs : IsOpen s := a.isOpen_inter_preimage hV
  let α := a.restr s
  let β := b.trans eH
  let A₃ : (Euc 1 × (C × ℝ)) ≃L[ℝ] Euc 3 :=
    (ContinuousLinearEquiv.prodAssoc ℝ (Euc 1) C ℝ).symm.trans
      ((A.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans tangentialNormalCL)
  have hαsource : α.source = a.source ∩ s := a.restr_source' s hs
  have hxα : x ∈ α.source := by
    rw [hαsource]
    exact ⟨mem_chart_source _ x, mem_chart_source _ x, hxV⟩
  have hαmax : α ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := by
    apply α.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_chart (I := 𝓡 1) (x := x)).mono inter_subset_left
    · exact (contMDiffOn_chart_symm (I := 𝓡 1) (x := x)).mono inter_subset_left
  have hβmax : β ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ N := by
    apply β.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas heH).comp
        ((contMDiffOn_chart (I := 𝓡∂ 3) (x := f x)).mono inter_subset_left) inter_subset_right
    · exact (contMDiffOn_chart_symm (I := 𝓡∂ 3) (x := f x)).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas heH).mono inter_subset_left) inter_subset_right
  have hread (y : Circle) (hy : y ∈ α.source) :
      a y ∈ V ∧ g₃ (a y) = (b.extend (𝓡∂ 3)) (f y) := by
    rw [hαsource] at hy
    refine ⟨hy.2.2, ?_⟩
    change (b.extend (𝓡∂ 3)) (f (a.symm (a y))) = _
    rw [a.left_inv hy.1]
  have hmap (y : Circle) (hy : y ∈ α.source) : f y ∈ β.source := by
    obtain ⟨hyV, hyread⟩ := hread y hy
    have hyU := hVU hyV
    have hyb : f y ∈ b.source := by
      have ht := hyU.2
      change f (a.symm (a y)) ∈ b.source at ht
      rw [a.left_inv ((hαsource ▸ hy).1)] at ht
      exact ht
    refine ⟨hyb, ?_⟩
    change (b (f y)).val ∈ e₃.source
    have ht : tangentialNormalCL.symm ((b.extend (𝓡∂ 3)) (f y)) = (g (a y), 0) := by
      rw [← hyread, hplane (a y) hyU, tangentialNormalCL.symm_apply_apply]
    change (b (f y)).val ∈ (liftTangentialChart e).source
    refine ⟨⟨mem_univ _, ?_⟩, mem_univ _⟩
    change (tangentialNormalCL.symm ((b.extend (𝓡∂ 3)) (f y))).1 ∈ e.source ∧ True
    rw [ht]
    exact ⟨(hstraight (a y) hyV).1, trivial⟩
  apply IsImmersionAt.mk_of_charts A₃ α β hxα (hmap x hxα) hαmax hβmax hmap
  intro z hz
  let y := (α.extend (𝓡 1)).symm z
  have hy : y ∈ α.source := by
    rw [← OpenPartialHomeomorph.extend_source (I := 𝓡 1)]
    exact (α.extend (𝓡 1)).map_target hz
  obtain ⟨hyV, hyread⟩ := hread y hy
  have hay : a y = z := by
    exact (α.extend (𝓡 1)).right_inv hz
  have ht : tangentialNormalCL.symm ((b.extend (𝓡∂ 3)) (f y)) = (g z, 0) := by
    rw [← hyread, hplane (a y) (hVU hyV), tangentialNormalCL.symm_apply_apply, hay]
  have hnormal : 0 ≤ (e₃ ((b.extend (𝓡∂ 3)) (f y))) 0 := by
    rw [liftTangentialChart_normal]
    exact (b (f y)).property
  change ((𝓡∂ 3) ((𝓡∂ 3).symm (e₃ ((b.extend (𝓡∂ 3)) (f y))))) = A₃ (z, 0)
  rw [(𝓡∂ 3).right_inv (by rw [range_modelWithCornersEuclideanHalfSpace]; exact hnormal)]
  change tangentialNormalCL (e (tangentialNormalCL.symm
    ((b.extend (𝓡∂ 3)) (f y))).1, (tangentialNormalCL.symm
    ((b.extend (𝓡∂ 3)) (f y))).2) = A₃ (z, 0)
  rw [ht, (hstraight z (hay ▸ hyV)).2]
  rfl

private theorem actual_curve_halfspace_immersion
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold (𝓡∂ 3) ∞ N] {f : Circle → N}
    (hf : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ f)
    (hi : ∀ z, IsDiffImmersionAt (𝓡 1) (𝓡∂ 3) f z)
    (hb : range f ⊆ (𝓡∂ 3).boundary N) :
    IsImmersion (𝓡 1) (𝓡∂ 3) ∞ f := by
  apply IsImmersionOfComplement.isImmersion (F := Euc 2)
  intro x
  let h := actual_curve_halfspace_immersionAt hf hi hb x
  let L := h.equiv.toLinearMap.comp (LinearMap.inr ℝ (Euc 1) h.complement)
  let _ : FiniteDimensional ℝ h.complement :=
    FiniteDimensional.of_injective L (h.equiv.injective.comp LinearMap.inr_injective)
  have hdim : Module.finrank ℝ h.complement = Module.finrank ℝ (Euc 2) := by
    have hsum := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at hsum
    norm_num (config := { congrConsts := false }) [Euc, finrank_euclideanSpace] at hsum ⊢
    omega
  exact h.isImmersionAtOfComplement_complement.trans_F (ContinuousLinearEquiv.ofFinrankEq hdim)

end
end SeifertSurfaces.GenusLinking.Continuation

namespace SeifertSurfaces.GenusLinking
open SeifertSurfaces.Foundations
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (L : OrientedLink n)
variable {T : TubularNeighborhood L} (E : SmoothExterior T)

theorem preferred_longitude_exists (Q : LinkCoordinates L) (i : Fin n) :
    ∃ c : C(Circle, E.Carrier), IsPreferredLongitude L E c i := by
  have hc : Continuous circleVector := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro r
    change Continuous (fun z : Circle => circleVector z r)
    have hcoe : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
    fin_cases r
    · simpa (config := { congrConsts := false }) [circleVector, PiLp.single_apply, Function.comp_def] using
        Complex.continuous_re.comp hcoe
    · simpa (config := { congrConsts := false }) [circleVector, PiLp.single_apply, Function.comp_def] using
        Complex.continuous_im.comp hcoe
  have hmem (p : TubeDomain) (hp : ‖(p.2 : Euc 2)‖ = 1) :
      T.tube i p ∈ T.exteriorSet := by
    change T.tube i p ∉ ⋃ j, T.openTube j
    intro hz
    obtain ⟨j, q, hq, hqeq⟩ := Set.mem_iUnion.mp hz
    by_cases hji : j = i
    · subst j
      have heq := (T.smoothEmbedding i).isEmbedding.injective hqeq
      rw [heq] at hq
      change ‖(p.2 : Euc 2)‖ < 1 at hq
      rw [hp] at hq
      exact lt_irrefl _ hq
    · exact Set.disjoint_left.mp (T.disjoint (Ne.symm hji)) ⟨p, rfl⟩ ⟨q, hqeq⟩
  let coords (k : ℤ) : C(Circle, TubeDomain) :=
    ⟨fun z => (z, ⟨circleVector (z ^ k), circleVector_mem_disk (z ^ k)⟩),
      continuous_id.prodMk (((hc.comp (continuous_id.zpow k))).subtype_mk _)⟩
  let slope (k : ℤ) : C(Circle, E.Carrier) :=
    ⟨fun z => ⟨T.tube i (coords k z), hmem (coords k z) (circleVector_norm (z ^ k))⟩,
      ((T.smoothEmbedding i).isEmbedding.continuous.comp (coords k).continuous).subtype_mk _⟩
  let meridian : C(Circle, E.Carrier) :=
    ⟨fun z => ⟨T.tube i (1, ⟨circleVector z, circleVector_mem_disk z⟩),
      hmem (1, ⟨circleVector z, circleVector_mem_disk z⟩) (circleVector_norm z)⟩,
      ((T.smoothEmbedding i).isEmbedding.continuous.comp
        (continuous_const.prodMk (hc.subtype_mk _))).subtype_mk _⟩
  let inclusion : C(E.Carrier, knotComplement (componentKnot L i)) :=
    ⟨exteriorToKnotComplement L E i, exteriorToKnotComplement_continuous L E i⟩
  let a : ℤ := linkingWithKnot (Q i) (inclusion.comp (slope 0))
  let d : ℤ := linkingWithKnot (Q i) (inclusion.comp meridian)
  have hd : d = 1 ∨ d = -1 := by
    let R : TubularNeighborhood (componentKnot L i) :=
      { tube := fun _ => T.tube i
        smoothEmbedding := fun _ => T.smoothEmbedding i
        core := fun _ => T.core i
        image_open := fun _ => T.image_open i
        disjoint := fun _ _ h => (h (Subsingleton.elim _ _)).elim }
    have hcurve : inclusion.comp meridian = tubeMeridian R := by
      ext z : 1
      apply Subtype.ext
      rfl
    change linkingWithKnot (Q i) (inclusion.comp meridian) = 1 ∨
      linkingWithKnot (Q i) (inclusion.comp meridian) = -1
    rw [hcurve]
    obtain ⟨k, hk, _⟩ := PositiveMeridianConstruction.knot_meridian_generates R
      ((Q i).coordinate.symm 1)
    change k • curveClass (tubeMeridian R) = (Q i).coordinate.symm 1 at hk
    have hone : k * linkingWithKnot (Q i) (tubeMeridian R) = 1 := by
      have h := congrArg (Q i).coordinate hk
      simpa (config := { congrConsts := false }) only [map_zsmul, LinearEquiv.apply_symm_apply, linkingWithKnot,
        zsmul_eq_mul, Int.cast_id] using h
    exact Int.eq_one_or_neg_one_of_mul_eq_one (by simpa (config := { congrConsts := false }) only [mul_comm] using hone)
  -- Actual torus homology calculation for the explicitly constructed slopes.
  have hformula (k : ℤ) : linkingWithKnot (Q i) (inclusion.comp (slope k)) =
      a + k * d := by
    let Torus : Type := Circle × Circle
    let TorusSSet := TopCat.toSSet.obj (TopCat.of Torus)
    let TorusOp1 : Type := ((integralChains Torus).opcycles 1 : Type)
    
    let simplexFace (i : Fin 3) : C(StdSimplex ℝ (Fin 2), StdSimplex ℝ (Fin 3)) :=
      ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩
    
    let torusEdgeClass (s : C(StdSimplex ℝ (Fin 2), Torus)) : TorusOp1 :=
      (TorusSSet.ιChainComplex ((TopCat.toSSetObjEquiv (TopCat.of Torus) (.op ⦋1⦌)).symm s) ≫
        (integralChains Torus).pOpcycles 1) 1
    
    have torusEdgeClass_boundary (s : C(StdSimplex ℝ (Fin 3), Torus)) :
        torusEdgeClass (s.comp (simplexFace 0)) - torusEdgeClass (s.comp (simplexFace 1)) +
          torusEdgeClass (s.comp (simplexFace 2)) = 0 := by
      let t := (TopCat.toSSetObjEquiv (TopCat.of Torus) (.op ⦋2⦌)).symm s
      have hf (i : Fin 3) : TorusSSet.δ i t =
          (TopCat.toSSetObjEquiv (TopCat.of Torus) (.op ⦋1⦌)).symm (s.comp (simplexFace i)) := by
        apply (TopCat.toSSetObjEquiv (TopCat.of Torus) (.op ⦋1⦌)).injective
        ext z : 1
        rfl
      have h : TorusSSet.ιChainComplex t ≫
          (TorusSSet.chainComplex (ModuleCat.of ℤ ℤ)).d (1 + 1) 1 ≫
          (integralChains Torus).pOpcycles 1 = 0 := by
        change TorusSSet.ιChainComplex t ≫ (integralChains Torus).d 2 1 ≫
          (integralChains Torus).pOpcycles 1 = 0
        simp (config := { congrConsts := false })
      rw [SSet.ιChainComplex_d_assoc] at h
      simp (config := { congrConsts := false }) only [Preadditive.sum_comp, Preadditive.zsmul_comp] at h
      have he := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ (integralChains Torus).opcycles 1 => f 1) h
      simpa (config := { congrConsts := false }) [Fin.sum_univ_succ, hf, torusEdgeClass, sub_eq_add_neg, add_assoc] using he
    
    let torusAffineEdge (a b : ℝ × ℝ) : C(StdSimplex ℝ (Fin 2), Torus) :=
      ⟨fun z => (Circle.exp (a.1 * z.weights 0 + b.1 * z.weights 1),
        Circle.exp (a.2 * z.weights 0 + b.2 * z.weights 1)), by fun_prop⟩
    
    let torusAffineTriangle (a b c : ℝ × ℝ) : C(StdSimplex ℝ (Fin 3), Torus) :=
      ⟨fun z => (Circle.exp (a.1 * z.weights 0 + b.1 * z.weights 1 + c.1 * z.weights 2),
        Circle.exp (a.2 * z.weights 0 + b.2 * z.weights 1 + c.2 * z.weights 2)), by fun_prop⟩
    
    have face_weights (i : Fin 3) (z : StdSimplex ℝ (Fin 2)) (j : Fin 3) :
        (simplexFace i z).weights j =
          ∑ k : Fin 2, if i.succAbove k = j then z.weights k else 0 := by
      simp (config := { congrConsts := false }) [simplexFace, StdSimplex.weights_map, Finsupp.mapDomain_fintype,
        Finsupp.single_apply]
    
    have torusAffineEdge_triangle (a b c : ℝ × ℝ) :
        torusEdgeClass (torusAffineEdge b c) - torusEdgeClass (torusAffineEdge a c) +
          torusEdgeClass (torusAffineEdge a b) = 0 := by
      have h := torusEdgeClass_boundary (torusAffineTriangle a b c)
      have hf (i : Fin 3) :
          (torusAffineTriangle a b c).comp (simplexFace i) =
            if i = 0 then torusAffineEdge b c else
              if i = 1 then torusAffineEdge a c else torusAffineEdge a b := by
        fin_cases i <;> ext z : 1 <;>
          simp (config := { congrConsts := false }) [torusAffineTriangle, torusAffineEdge, face_weights, Fin.sum_univ_two,
            Fin.succAbove]
      simpa (config := { congrConsts := false }) [hf] using h
    
    let torusLoopEdge (p : ℤ × ℤ) : C(StdSimplex ℝ (Fin 2), Torus) :=
      torusAffineEdge (0, 0) (p.1 * (2 * Real.pi), p.2 * (2 * Real.pi))
    
    have torusAffineEdge_period_shift (a b : ℝ × ℝ) (p : ℤ × ℤ) :
        torusAffineEdge (a.1 + p.1 * (2 * Real.pi), a.2 + p.2 * (2 * Real.pi))
          (b.1 + p.1 * (2 * Real.pi), b.2 + p.2 * (2 * Real.pi)) = torusAffineEdge a b := by
      ext z : 1
      have hz : z.weights 0 + z.weights 1 = 1 := by
        simp (config := { congrConsts := false })
      apply Prod.ext
      all_goals
        simp (config := { congrConsts := false }) only [torusAffineEdge, ContinuousMap.coe_mk]
        apply Circle.exp_eq_exp.mpr
      · refine ⟨p.1, ?_⟩
        calc
          _ = a.1 * z.weights 0 + b.1 * z.weights 1 +
            p.1 * (2 * Real.pi) * (z.weights 0 + z.weights 1) := by ring
          _ = _ := by rw [hz, mul_one]
      · refine ⟨p.2, ?_⟩
        calc
          _ = a.2 * z.weights 0 + b.2 * z.weights 1 +
            p.2 * (2 * Real.pi) * (z.weights 0 + z.weights 1) := by ring
          _ = _ := by rw [hz, mul_one]
    
    have torusLoopEdge_add (p q : ℤ × ℤ) :
        torusEdgeClass (torusLoopEdge (p + q)) =
          torusEdgeClass (torusLoopEdge p) + torusEdgeClass (torusLoopEdge q) := by
      have hf : torusAffineEdge (p.1 * (2 * Real.pi), p.2 * (2 * Real.pi))
          ((p + q).1 * (2 * Real.pi), (p + q).2 * (2 * Real.pi)) = torusLoopEdge q := by
        have h := torusAffineEdge_period_shift (0, 0)
          (q.1 * (2 * Real.pi), q.2 * (2 * Real.pi)) p
        have he (a b : ℤ) : ((a + b : ℤ) : ℝ) * (2 * Real.pi) =
            b * (2 * Real.pi) + a * (2 * Real.pi) := by push_cast; ring
        simpa (config := { congrConsts := false }) only [torusLoopEdge, Prod.fst_add, Prod.snd_add, he, zero_add] using h
      have ht := torusAffineEdge_triangle (0, 0)
        (p.1 * (2 * Real.pi), p.2 * (2 * Real.pi))
        ((p + q).1 * (2 * Real.pi), (p + q).2 * (2 * Real.pi))
      rw [hf] at ht
      change _ - torusEdgeClass (torusLoopEdge (p + q)) + torusEdgeClass (torusLoopEdge p) = 0 at ht
      apply sub_eq_zero.mp
      calc
        _ = -(torusEdgeClass (torusLoopEdge q) - torusEdgeClass (torusLoopEdge (p + q)) +
          torusEdgeClass (torusLoopEdge p)) := by abel
        _ = 0 := by rw [ht, neg_zero]
    
    have torusLoopEdge_formula (k : ℤ) :
        torusEdgeClass (torusLoopEdge (1, k)) = torusEdgeClass (torusLoopEdge (1, 0)) +
          k • torusEdgeClass (torusLoopEdge (0, 1)) := by
      let h : (ℤ × ℤ) →+ TorusOp1 :=
        { toFun := fun p => torusEdgeClass (torusLoopEdge p)
          map_zero' := by
            have hz := torusLoopEdge_add (0 : ℤ × ℤ) 0
            apply add_left_cancel (a := torusEdgeClass (torusLoopEdge 0))
            simpa (config := { congrConsts := false }) only [zero_add, add_zero] using hz.symm
          map_add' := torusLoopEdge_add }
      have hp : ((1, k) : ℤ × ℤ) = (1, 0) + k • ((0, 1) : ℤ × ℤ) := by ext <;> simp (config := { congrConsts := false })
      change h (1, k) = h (1, 0) + k • h (0, 1)
      rw [hp, map_add, map_zsmul]
    
    let torusLoop (p : ℤ × ℤ) : C(Circle, Torus) :=
      ⟨fun z => (z ^ p.1, z ^ p.2), by fun_prop⟩
    
    have torusLoop_edge (p : ℤ × ℤ) :
        TopCat.toSSetObjEquiv (TopCat.of Torus) (.op ⦋1⦌)
          ((TopCat.toSSet.map (TopCat.ofHom (torusLoop p))).app (.op ⦋1⦌) circleLoopSimplex) =
          torusLoopEdge p := by
      ext z : 1
      apply Prod.ext
      · change Circle.exp (2 * Real.pi * z.weights 1) ^ p.1 =
          Circle.exp (0 * z.weights 0 + ((p.1 : ℝ) * (2 * Real.pi)) * z.weights 1)
        rw [← Circle.exp_intCast_mul]
        congr 1
        ring
      · change Circle.exp (2 * Real.pi * z.weights 1) ^ p.2 =
          Circle.exp (0 * z.weights 0 + ((p.2 : ℝ) * (2 * Real.pi)) * z.weights 1)
        rw [← Circle.exp_intCast_mul]
        congr 1
        ring
    
    have torusLoop_opcycles (p : ℤ × ℤ) :
        (integralChains Torus).homologyι 1 (curveClass (torusLoop p)) =
          torusEdgeClass (torusLoopEdge p) := by
      let M := (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (torusLoop p)))
      change (((integralChains Circle).liftCycles circleLoopChain 0 (by simp (config := { congrConsts := false })) circleLoopChain_boundary ≫
        (integralChains Circle).homologyπ 1) ≫ HomologicalComplex.homologyMap M 1 ≫
          (integralChains Torus).homologyι 1) 1 = _
      rw [HomologicalComplex.homologyι_naturality]
      simp (config := { congrConsts := false }) only [Category.assoc]
      rw [HomologicalComplex.homology_π_ι_assoc,
        HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.p_opcyclesMap]
      have hm : circleLoopChain ≫ M.f 1 =
          TorusSSet.ιChainComplex
            ((TopCat.toSSetObjEquiv (TopCat.of Torus) (.op ⦋1⦌)).symm (torusLoopEdge p)) := by
        change (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex circleLoopSimplex ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (torusLoop p)))
            (ModuleCat.of ℤ ℤ)).f 1 = _
        rw [SSet.ι_chainComplexMap_f]
        congr 1
        exact (TopCat.toSSetObjEquiv (TopCat.of Torus) (.op ⦋1⦌)).injective (by
          rw [torusLoop_edge, Equiv.apply_symm_apply])
      rw [← Category.assoc, hm]
    
    have torusLoop_homology_formula (k : ℤ) :
        curveClass (torusLoop (1, k)) = curveClass (torusLoop (1, 0)) +
          k • curveClass (torusLoop (0, 1)) := by
      have hinj : Function.Injective ((integralChains Torus).homologyι 1) :=
        (ModuleCat.mono_iff_injective ((integralChains Torus).homologyι 1)).mp inferInstance
      apply hinj
      simp (config := { congrConsts := false }) only [map_add, map_zsmul, torusLoop_opcycles]
      exact torusLoopEdge_formula k
    
    have curveClass_torusSlope {X : Type} [TopologicalSpace X]
        (c : C(Torus, X)) (k : ℤ) :
        curveClass (c.comp (torusLoop (1, k))) = curveClass (c.comp (torusLoop (1, 0))) +
          k • curveClass (c.comp (torusLoop (0, 1))) := by
      let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)
      have hn (p : ℤ × ℤ) : curveClass (c.comp (torusLoop p)) =
          (H.map (TopCat.ofHom c)) (curveClass (torusLoop p)) := by
        unfold curveClass
        rw [← ModuleCat.comp_apply, ← Functor.map_comp]
        rfl
      simp_rw (config := { congrConsts := false }) [hn]
      rw [torusLoop_homology_formula, map_add, map_zsmul]
    let f : C(Torus, E.Carrier) :=
      ⟨fun z => ⟨T.tube i (z.1, ⟨circleVector z.2, circleVector_mem_disk z.2⟩),
        hmem (z.1, ⟨circleVector z.2, circleVector_mem_disk z.2⟩) (circleVector_norm z.2)⟩,
        ((T.smoothEmbedding i).isEmbedding.continuous.comp
          (continuous_fst.prodMk ((hc.comp continuous_snd).subtype_mk _))).subtype_mk _⟩
    let tubeMap : C(Torus, knotComplement (componentKnot L i)) := inclusion.comp f
    have hs (l : ℤ) : tubeMap.comp (torusLoop (1, l)) = inclusion.comp (slope l) := by
      ext z : 1
      apply Subtype.ext
      simp (config := { congrConsts := false }) [tubeMap, f, torusLoop, slope, coords, inclusion]
    have hm : tubeMap.comp (torusLoop (0, 1)) = inclusion.comp meridian := by
      ext z : 1
      apply Subtype.ext
      simp (config := { congrConsts := false }) [tubeMap, f, torusLoop, meridian, inclusion]
    have ht := congrArg (Q i).coordinate (curveClass_torusSlope tubeMap k)
    rw [hs k, hs 0, hm, map_add, map_zsmul] at ht
    simpa (config := { congrConsts := false }) only [a, d, linkingWithKnot, zsmul_eq_mul, Int.cast_id] using ht

  -- Smooth slope bridge for the chosen exterior corner structure.
  have hsmooth (k : ℤ) : Manifold.IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ (slope k) := by
    have circleVector_smooth : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ circleVector := by
      let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp (config := { congrConsts := false })⟩
      let A : ℂ →ₗ[ℝ] Euc 2 :=
        (LinearMap.toSpanSingleton ℝ (Euc 2) (EuclideanSpace.single 0 1)).comp
          Complex.reLm +
        (LinearMap.toSpanSingleton ℝ (Euc 2) (EuclideanSpace.single 1 1)).comp
          Complex.imLm
      let B : ℂ →L[ℝ] Euc 2 := A.toContinuousLinearMap
      have hB : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ (fun z : Circle => B (z : ℂ)) :=
        B.contDiff.contMDiff.comp contMDiff_coe_sphere
      convert hB using 1
      funext z
      ext j
      simp (config := { congrConsts := false }) [B, A, circleVector, LinearMap.toSpanSingleton_apply, PiLp.single_apply]
    
    have circle_zpow_smooth (k : ℤ) : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z ^ k) := by
      cases k with
      | ofNat k => simpa (config := { congrConsts := false }) using (contMDiff_id.pow k : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z ^ k))
      | negSucc k =>
        simpa (config := { congrConsts := false }) [zpow_negSucc] using
          ((contMDiff_id.pow (k + 1)).inv : ContMDiff (𝓡 1) (𝓡 1) ∞
            (fun z : Circle => (z ^ (k + 1))⁻¹))
    
    have slope_coordinates_smooth (k : ℤ) :
        ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, Euc 2)) ∞
          (fun z : Circle => (z, (⟨circleVector (z ^ k), circleVector_mem_disk (z ^ k)⟩ : TubeDisk))) := by
      apply ContMDiff.prodMk contMDiff_id
      apply (ContMDiff.subtypeVal_comp_iff tubeDiskOpen _).mp
      exact circleVector_smooth.comp (circle_zpow_smooth k)
    have hcoords : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, Euc 2)) ∞ (coords k) :=
      slope_coordinates_smooth k
    have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
    have hs : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ (slope k) := by
      apply (ContMDiff.iff_comp_isImmersion hinc.isImmersion).mpr
      exact ⟨(slope k).continuous, (T.smoothEmbedding i).contMDiff.comp hcoords⟩
    have hi : Function.Injective (slope k) := by
      intro z w hzw
      have ht : T.tube i (coords k z) = T.tube i (coords k w) := congrArg Subtype.val hzw
      exact congrArg Prod.fst ((T.smoothEmbedding i).isEmbedding.injective ht)
    have htop : IsEmbedding (slope k) := ((slope k).continuous.isClosedEmbedding hi).isEmbedding
    have hdiffcoords (z : Circle) :
        IsDiffImmersionAt (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, Euc 2)) (coords k) z := by
      have hid : IsDiffImmersionAt (𝓡 1) (𝓡 1) (id : Circle → Circle) z :=
        (Manifold.IsImmersion.id (I := 𝓡 1) (n := ∞)).isDiffImmersionAt (by simp (config := { congrConsts := false })) z
      apply IsDiffImmersionAt.of_comp (hcoords.mdifferentiableAt (by simp (config := { congrConsts := false })))
        ((contMDiff_fst (n := ∞)).mdifferentiableAt (by simp (config := { congrConsts := false })))
      exact hid
    have hdiff (z : Circle) : IsDiffImmersionAt (𝓡 1) (𝓡∂ 3) (slope k) z := by
      apply IsDiffImmersionAt.of_comp (hs.mdifferentiableAt (by simp (config := { congrConsts := false })))
        (hinc.contMDiff.mdifferentiableAt (by simp (config := { congrConsts := false })))
      exact ((T.smoothEmbedding i).isImmersion.isDiffImmersionAt (by simp (config := { congrConsts := false })) (coords k z)).comp
        (hdiffcoords z)
    have hboundary : Set.range (slope k) ⊆ (𝓡∂ 3).boundary E.Carrier := by
      rintro x ⟨z, rfl⟩
      have hbi : (Subtype.val : E.Carrier → ThreeSphere) ''
          ((𝓡∂ 3).boundary E.Carrier) = ⋃ i, T.shell i := E.boundary_image
      have hx : E.toSphere (slope k z) ∈ (Subtype.val : E.Carrier → ThreeSphere) ''
          ((𝓡∂ 3).boundary E.Carrier) := by
        rw [hbi]
        exact Set.mem_iUnion.mpr ⟨i, coords k z, circleVector_norm (z ^ k), rfl⟩
      obtain ⟨x, hxb, hx⟩ := hx
      exact (Subtype.ext hx : x = slope k z) ▸ hxb
    -- Straighten tangential coordinates while fixing the halfspace normal.
    have himmersion : Manifold.IsImmersion (𝓡 1) (𝓡∂ 3) ∞ (slope k) := by
      exact Continuation.actual_curve_halfspace_immersion hs hdiff hboundary
    exact ⟨himmersion, htop⟩

  let k : ℤ := -a * d
  refine ⟨slope k, hsmooth k, ?_, ?_, ?_⟩
  · rintro x ⟨z, rfl⟩
    change T.tube i (coords k z) ∈ T.shell i
    exact ⟨coords k z, circleVector_norm (z ^ k), rfl⟩
  · refine ⟨coords k, fun _ => rfl, ?_⟩
    exact ContinuousMap.Homotopic.refl (ContinuousMap.id Circle)
  · apply (Q i).coordinate.injective
    change linkingWithKnot (Q i) (inclusion.comp (slope k)) = (Q i).coordinate 0
    rw [hformula, map_zero]
    rcases hd with he | he <;> simp (config := { congrConsts := false }) [k, he]

theorem spanning_longitude_preferred_iff (Q : LinkCoordinates L)
    (F : LinkSpanningSurface.{0} E) (i : Fin n) :
    IsPreferredLongitude L E (boundaryExteriorCurve L E F i) i ↔
      (∑ j ∈ Finset.univ.erase i, componentLinking L Q j i) = 0 := by
  have hsmooth : Manifold.IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞
      (boundaryExteriorCurve L E F i) := by
    have hs : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ (boundaryExteriorCurve L E F i) :=
      F.embedding.smoothEmbedding.contMDiff.comp
        (F.boundaryCircle i).smoothEmbedding.contMDiff
    have htop : IsEmbedding (boundaryExteriorCurve L E F i) :=
      F.embedding.smoothEmbedding.isEmbedding.comp
        (F.boundaryCircle i).smoothEmbedding.isEmbedding
    have hdiff (z : Circle) : IsDiffImmersionAt (𝓡 1) (𝓡∂ 3)
        (boundaryExteriorCurve L E F i) z :=
      (F.embedding.smoothEmbedding.isImmersion.isDiffImmersionAt (by simp (config := { congrConsts := false }))
        ((F.boundaryCircle i).toFun z)).comp
        ((F.boundaryCircle i).smoothEmbedding.isImmersion.isDiffImmersionAt (by simp (config := { congrConsts := false })) z)
    have hboundary : Set.range (boundaryExteriorCurve L E F i) ⊆
        (𝓡∂ 3).boundary E.Carrier := by
      rintro x ⟨z, rfl⟩
      change (F.boundaryCircle i).toFun z ∈ F.embedding.toFun ⁻¹' (𝓡∂ 3).boundary E.Carrier
      rw [F.embedding.boundary_preimage]
      exact (F.boundaryCircle i).lands_boundary z
    -- Straighten tangential coordinates while fixing the halfspace normal.
    have himmersion : Manifold.IsImmersion (𝓡 1) (𝓡∂ 3) ∞
        (boundaryExteriorCurve L E F i) := by
      exact Continuation.actual_curve_halfspace_immersion hs hdiff hboundary
    exact ⟨himmersion, htop⟩
  have htorus : Set.range (boundaryExteriorCurve L E F i) ⊆ E.boundaryTorus i := by
    rintro x ⟨z, rfl⟩
    change E.toSphere (F.embedding.toFun ((F.boundaryCircle i).toFun z)) ∈ T.shell i
    exact ⟨F.coordinates i z, F.on_shell i z, (F.boundary_tube i z).symm⟩
  have hcoords : ∃ coords : C(Circle, TubeDomain),
      (∀ z, T.tube i (coords z) = E.toSphere ((boundaryExteriorCurve L E F i) z)) ∧
      ContinuousMap.Homotopic
        (⟨fun z => (coords z).1, continuous_fst.comp coords.continuous⟩ : C(Circle, Circle))
        (ContinuousMap.id Circle) :=
    ⟨F.coordinates i, fun z => (F.boundary_tube i z).symm, F.longitudinal_degree_one i⟩
  have hnull : curveClass (boundaryInComplement L E F i i) = 0 ↔
      (∑ j ∈ Finset.univ.erase i, componentLinking L Q j i) = 0 := by
    rw [← (Q i).coordinate.map_eq_zero_iff]
    change linkingWithKnot (Q i) (boundaryInComplement L E F i i) = 0 ↔ _
    rw [surface_framed_longitude_linking L E Q F i, neg_eq_zero]
  constructor
  · intro hpreferred
    exact hnull.mp hpreferred.2.2.2
  · intro hsum
    exact ⟨hsmooth, htorus, hcoords, hnull.mpr hsum⟩

/-- Finite actual component indexing follows from compact local connectivity;
no finite CW hypothesis is imposed on the spanning surface. -/
theorem separate_component_linking_zero (Q : LinkCoordinates L)
    (F : LinkSpanningSurface.{0} E) (j : Fin n) (c : ConnectedComponents F.surface)
    (hc : c ≠ boundaryComponent L E F j) :
    (∑ i ∈ Finset.univ.filter (fun i => boundaryComponent L E F i = c),
      componentLinking L Q j i) = 0 := by
  have hz := congrArg (Q j).coordinate (component_boundary_homology_zero L E F c j)
  rw [map_sum, map_zero] at hz
  calc
    (∑ i ∈ Finset.univ.filter (fun i => boundaryComponent L E F i = c),
        componentLinking L Q j i) =
      ∑ i ∈ Finset.univ.filter (fun i => boundaryComponent L E F i = c),
        (Q j).coordinate (curveClass (boundaryInComplement L E F i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hic := (Finset.mem_filter.mp hi).2
      have hij : i ≠ j := by
        intro hij
        subst i
        exact hc hic.symm
      rw [componentLinking_symmetric L Q j i]
      simp (config := { congrConsts := false }) only [componentLinking, dite_eq_right hij, linkingWithKnot]
      rw [boundary_other_component_homology L E F i j hij]
    _ = 0 := hz

/-- Geometric Lemma 6.1, with real spanning surfaces, connected components,
and computed homological linking. Connectedness is the conclusion. -/
theorem spanning_connected_of_linkingIndecomposable (Q : LinkCoordinates L)
    (h : LinkIsLinkingIndecomposable L Q) (F : LinkSpanningSurface.{0} E) :
    ConnectedSpace F.surface := by
  classical
  let k : Fin n := ⟨0, L.nonempty⟩
  have hall (i : Fin n) : boundaryComponent L E F i = boundaryComponent L E F k := by
    by_contra hik
    let I : Finset (Fin n) := Finset.univ.filter
      (fun j => boundaryComponent L E F j = boundaryComponent L E F i)
    have hiI : i ∈ I := by simp (config := { congrConsts := false }) [I]
    have hkI : k ∈ Iᶜ := by simp (config := { congrConsts := false }) [I, Ne.symm hik]
    obtain ⟨m, hm⟩ := h I ⟨i, hiI⟩ ⟨k, hkI⟩
    by_cases hmI : m ∈ I
    · have hmi : boundaryComponent L E F m = boundaryComponent L E F i :=
        (Finset.mem_filter.mp hmI).2
      let C : Finset (ConnectedComponents F.surface) :=
        Iᶜ.image (boundaryComponent L E F)
      have hC (c : ConnectedComponents F.surface) (hc : c ∈ C) :
          c ≠ boundaryComponent L E F i := by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
        simpa (config := { congrConsts := false }) [I] using hj
      have hzero : (∑ j ∈ Iᶜ, componentLinking L Q m j) = 0 := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := Iᶜ) (t := C)
          (g := boundaryComponent L E F)
          (fun j hj => Finset.mem_image.mpr ⟨j, hj, rfl⟩)
          (componentLinking L Q m)]
        apply Finset.sum_eq_zero
        intro c hc
        have hci := hC c hc
        have heq : Iᶜ.filter (fun j => boundaryComponent L E F j = c) =
            Finset.univ.filter (fun j => boundaryComponent L E F j = c) := by
          ext j
          simp (config := { congrConsts := false }) only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact And.right
          · intro hjc
            refine ⟨?_, hjc⟩
            simp (config := { congrConsts := false }) only [Finset.mem_compl, I, Finset.mem_filter, Finset.mem_univ, true_and]
            intro hji
            exact hci (hjc.symm.trans hji)
        rw [heq]
        exact separate_component_linking_zero L E Q F m c (by simpa (config := { congrConsts := false }) [hmi] using hci)
      exact hm (by simpa (config := { congrConsts := false }) [hmI] using hzero)
    · have hci : boundaryComponent L E F i ≠ boundaryComponent L E F m := by
        intro him
        apply hmI
        simp (config := { congrConsts := false }) [I, him]
      have hzero := separate_component_linking_zero L E Q F m
        (boundaryComponent L E F i) hci
      exact hm (by simpa (config := { congrConsts := false }) [hmI, I] using hzero)
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨(F.boundaryCircle k).toFun 1, Set.eq_univ_of_forall ?_⟩
  intro x
  obtain ⟨i, hi⟩ := boundaryComponent_surjective L E F (ConnectedComponents.mk x)
  apply ConnectedComponents.coe_eq_coe'.mp
  exact hi.symm.trans (hall i)

theorem spanning_boundary_count_and_connected (Q : LinkCoordinates L)
    (h : LinkIsLinkingIndecomposable L Q) (F : LinkSpanningSurface.{0} E) :
    ConnectedSpace F.surface ∧ boundaryCount F.surface = n := by
  exact ⟨spanning_connected_of_linkingIndecomposable L E Q h F,
    spanning_boundary_count E F⟩

end
end SeifertSurfaces.GenusLinking

end
