import B1NativeUpperComparison_v468
import Lean
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exposes the literal witnesses of the already paid native Dirichlet constructor.
The proof is obtained from its actual body and rechecked by the kernel. -/
theorem actual_halfdisc_pair_weak_literal_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (R : ℝ) (hRW : R < W.R) (p : X (halfDisc R))
    (hsolve : ∀ q : X (halfDisc R),
      (∫ x in halfDisc R,
        inner ℝ (matrixAction (W.a x) (grad (halfDisc R) p x)) (grad (halfDisc R) q x) -
        (inner ℝ (W.b x) (grad (halfDisc R) p x) + W.c x * val (halfDisc R) p x) * val (halfDisc R) q x) =
      ∫ x in halfDisc R, W.c x * val (halfDisc R) q x) :
    H1On (halfDisc R) (fun x => val (halfDisc R) p x + 1) (grad (halfDisc R) p) ∧
    H10On (halfDisc R) (fun x => val (halfDisc R) p x + 1 - 1) (grad (halfDisc R) p) ∧
    WeakLinearEquationOn (halfDisc R) W.a W.b W.c
      (fun x => val (halfDisc R) p x + 1) (grad (halfDisc R) p) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let env := (← Lean.getEnv).setExporting false
    let some ci := env.find? `SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_halfdisc_pair_to_weak_v468 |
      throwError "paid native constructor absent"
    let some raw := ci.value? (allowOpaque := true) | throwError "paid native constructor body absent"
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let mut value := raw.beta args
    for _ in [:2] do
      value ← Lean.Meta.withTransparency .all <| Lean.Meta.whnf value
      unless value.getAppFn.isConstOf `Exists.intro do
        throwError "paid native constructor witness shape changed: {value.getAppFn}"
      value := value.getAppArgs.back!
    Lean.Meta.checkWithKernel value
    (← Lean.Elab.Tactic.getMainGoal).assign value
    Lean.Elab.Tactic.replaceMainGoal []

end SeifertSurfaces.OriginalEndpoints.B1Tangency
